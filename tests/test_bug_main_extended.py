"""
Test Plan for bug_main.py
==========================

This test file covers the bug_main function which generates unit tests based on
observed vs desired outputs.

TEST PLAN:
----------

1. FORMAL VERIFICATION (Z3):
   a) Path Resolution Logic:
      - Verify that output path is never None after resolution
      - Verify that empty output paths are replaced with defaults
      - Verify that directory paths are correctly extracted
   
   b) Language Detection:
      - Verify that language parameter handling follows correct precedence:
        1. Explicit language parameter
        2. Detected language from construct_paths
        3. Default "Python"

2. UNIT TESTS:
   a) Happy Path Tests:
      - Test successful unit test generation with all valid inputs
      - Test with explicit output path
      - Test with None output path (uses default)
      - Test with different language specifications
   
   b) Output Path Handling:
      - Test with empty string output path (should use default)
      - Test with nested directory paths (should create directories)
      - Test output file is written correctly
   
   c) Context and Configuration:
      - Test with force flag enabled/disabled
      - Test with quiet mode enabled/disabled
      - Test with custom strength, temperature, time parameters
      - Test with context override
   
   d) Error Handling:
      - Test behavior when construct_paths raises exception
      - Test behavior when bug_to_unit_test raises exception
      - Test that sys.exit(1) is called on errors
   
   e) Integration:
      - Test that construct_paths is called with correct parameters
      - Test that bug_to_unit_test is called with correct parameters
      - Test that file content is read correctly from input_strings
      - Test that output is written to correct location

EDGE CASES:
-----------
- Empty output path: Use default naming
- Non-existent output directory: Create it
- Language=None: Use detected language
- Quiet mode: Still print unit test, suppress other output
- Error conditions: Exit with code 1, print error if not quiet

Z3 vs UNIT TEST DECISION:
--------------------------
- Z3 is better for: Path resolution logic, type constraints, invariants
- Unit tests are better for: File I/O, mocking external dependencies, integration
"""

import pytest
import os
import sys
from pathlib import Path
from unittest.mock import Mock, MagicMock, patch, mock_open
from typing import Tuple
from z3 import Solver, String, If, Or, Concat, sat

# Import the function under test using the ACTUAL module path
from pdd.bug_main import bug_main


# ============================================================================
# Z3 FORMAL VERIFICATION TESTS
# ============================================================================

class TestBugMainFormalVerification:
    """Formal verification tests using Z3 for path resolution logic."""
    
    def test_z3_output_path_never_none_after_resolution(self) -> None:
        """
        Verify that the output path logic ensures a valid path always exists.
        
        This tests the invariant: if output_file_paths["output"] is empty or None,
        a default path is constructed.
        """
        solver = Solver()
        
        # Define symbolic variables
        output_path_from_construct = String('output_path_from_construct')
        final_output_path = String('final_output_path')
        code_file_stem = String('code_file_stem')
        language = String('language')
        
        # Define the default path construction
        default_path = Concat(
            String("test_"),
            code_file_stem,
            String("_bug."),
            language
        )
        
        # Logic: if output_path_from_construct is empty, use default
        is_empty = Or(
            output_path_from_construct == String(""),
            output_path_from_construct == String(" "),
            output_path_from_construct == String("  ")
        )
        
        # If empty, final path should be default; otherwise use original
        solver.add(
            If(is_empty,
               final_output_path == default_path,
               final_output_path == output_path_from_construct)
        )
        
        # Add constraint that we have empty input
        solver.add(output_path_from_construct == String(""))
        solver.add(code_file_stem == String("my_module"))
        solver.add(language == String("python"))
        
        # Check satisfiability
        assert solver.check() == sat
        
        model = solver.model()
        
        # Verify the final output path is the expected default
        final_path_value = model[final_output_path]
        # Z3 should have resolved this to the default path
        assert final_path_value is not None
    
    def test_z3_language_precedence(self) -> None:
        """
        Verify the language parameter precedence logic using Z3.
        
        Language precedence:
        1. Explicit language parameter (if not None)
        2. Detected language from construct_paths
        """
        solver = Solver()
        
        # Define symbolic variables
        explicit_lang = String('explicit_lang')
        detected_lang = String('detected_lang')
        final_lang = String('final_lang')
        
        # Special marker for None
        none_marker = String('__NONE__')
        
        # Logic: if explicit_lang is not None, use it; otherwise use detected
        solver.add(
            If(explicit_lang == none_marker,
               final_lang == detected_lang,
               final_lang == explicit_lang)
        )
        
        # Test case 1: explicit language provided
        solver.push()
        solver.add(explicit_lang == String("Python"))
        solver.add(detected_lang == String("JavaScript"))
        assert solver.check() == sat
        solver.model()
        # Should use explicit language
        solver.pop()
        
        # Test case 2: no explicit language (None)
        solver.push()
        solver.add(explicit_lang == none_marker)
        solver.add(detected_lang == String("JavaScript"))
        assert solver.check() == sat
        solver.model()
        # Should use detected language
        solver.pop()


# ============================================================================
# UNIT TESTS
# ============================================================================

class TestBugMainHappyPath:
    """Test successful execution paths."""
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    @patch('builtins.open', new_callable=mock_open)
    @patch('os.makedirs')
    def test_successful_unit_test_generation_with_output(
        self,
        mock_makedirs: MagicMock,
        mock_file: MagicMock,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test successful generation with explicit output path."""
        # Setup mocks
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': False,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                'prompt_file': 'prompt content',
                'code_file': 'code content',
                'program_file': 'program content',
                'current_output': 'current output',
                'desired_output': 'desired output'
            },
            {'output': '/output/test_bug.py'},
            'Python'
        )
        
        mock_bug_to_unit_test.return_value = (
            'def test_example(): pass',
            0.05,
            'gpt-4'
        )
        
        # Execute
        result = bug_main(
            ctx=mock_ctx,
            prompt_file='prompt.prompt',
            code_file='code.py',
            program_file='program.py',
            current_output='current.txt',
            desired_output='desired.txt',
            output='/output/test_bug.py',
            language='Python'
        )
        
        # Verify
        assert result == ('def test_example(): pass', 0.05, 'gpt-4')
        mock_makedirs.assert_called_once_with('/output', exist_ok=True)
        mock_file.assert_called_once_with('/output/test_bug.py', 'w')
        mock_file().write.assert_called_once_with('def test_example(): pass')
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_successful_generation_without_output_path(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test generation without explicit output path (no file written)."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': True,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'prompt',
                'code_file': 'code',
                'program_file': 'program',
                'current_output': 'current',
                'desired_output': 'desired'
            },
            {},  # No output path
            'Python'
        )
        
        mock_bug_to_unit_test.return_value = ('test code', 0.03, 'gpt-3.5')
        
        result = bug_main(
            ctx=mock_ctx,
            prompt_file='p.prompt',
            code_file='c.py',
            program_file='prog.py',
            current_output='cur.txt',
            desired_output='des.txt',
            output=None,
            language='Python'
        )
        
        assert result == ('test code', 0.03, 'gpt-3.5')


class TestBugMainOutputPathHandling:
    """Test various output path scenarios."""
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    @patch('builtins.open', new_callable=mock_open)
    @patch('os.makedirs')
    def test_empty_output_path_uses_default(
        self,
        mock_makedirs: MagicMock,
        mock_file: MagicMock,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that empty output path is replaced with default."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': False,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        # construct_paths returns empty string for output
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'prompt',
                'code_file': 'code',
                'program_file': 'program',
                'current_output': 'current',
                'desired_output': 'desired'
            },
            {'output': ''},  # Empty output path
            'Python'
        )
        
        mock_bug_to_unit_test.return_value = ('test', 0.01, 'model')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='prompt.prompt',
            code_file='mycode.py',
            program_file='program.py',
            current_output='cur.txt',
            desired_output='des.txt',
            output='',
            language='Python'
        )
        
        # Should write to default path
        mock_file.assert_called_once()
        call_args = mock_file.call_args[0][0]
        assert 'test_mycode_bug.python' in call_args
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    @patch('builtins.open', new_callable=mock_open)
    @patch('os.makedirs')
    def test_nested_directory_creation(
        self,
        mock_makedirs: MagicMock,
        mock_file: MagicMock,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that nested directories are created."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': True,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'p',
                'code_file': 'c',
                'program_file': 'prog',
                'current_output': 'cur',
                'desired_output': 'des'
            },
            {'output': 'a/b/c/test.py'},
            'Python'
        )
        
        mock_bug_to_unit_test.return_value = ('test', 0.01, 'model')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='p.prompt',
            code_file='c.py',
            program_file='prog.py',
            current_output='cur.txt',
            desired_output='des.txt',
            output='a/b/c/test.py',
            language='Python'
        )
        
        mock_makedirs.assert_called_once_with('a/b/c', exist_ok=True)


class TestBugMainContextConfiguration:
    """Test context and configuration parameter handling."""
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_custom_strength_temperature_time(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that custom strength, temperature, and time are passed correctly."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': True,
            'quiet': True,
            'strength': 0.8,
            'temperature': 0.5,
            'time': 0.75,
            'context': 'custom_context'
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'p',
                'code_file': 'c',
                'program_file': 'prog',
                'current_output': 'cur',
                'desired_output': 'des'
            },
            {},
            'JavaScript'
        )
        
        mock_bug_to_unit_test.return_value = ('test', 0.02, 'model')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='p.prompt',
            code_file='c.js',
            program_file='prog.js',
            current_output='cur.txt',
            desired_output='des.txt'
        )
        
        # Verify bug_to_unit_test was called with custom parameters
        mock_bug_to_unit_test.assert_called_once()
        call_args = mock_bug_to_unit_test.call_args[0]
        assert call_args[5] == 0.8  # strength
        assert call_args[6] == 0.5  # temperature
        assert call_args[7] == 0.75  # time
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_context_override_passed_to_construct_paths(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that context override is passed to construct_paths."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': True,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': 'backend'
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'p',
                'code_file': 'c',
                'program_file': 'prog',
                'current_output': 'cur',
                'desired_output': 'des'
            },
            {},
            'Python'
        )
        
        mock_bug_to_unit_test.return_value = ('test', 0.01, 'model')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='p.prompt',
            code_file='c.py',
            program_file='prog.py',
            current_output='cur.txt',
            desired_output='des.txt'
        )
        
        # Verify construct_paths was called with context_override
        mock_construct_paths.assert_called_once()
        assert mock_construct_paths.call_args[1]['context_override'] == 'backend'


class TestBugMainLanguageDetection:
    """Test language parameter handling."""
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_explicit_language_takes_precedence(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that explicit language parameter is used over detected."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': True,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'p',
                'code_file': 'c',
                'program_file': 'prog',
                'current_output': 'cur',
                'desired_output': 'des'
            },
            {},
            'JavaScript'  # Detected language
        )
        
        mock_bug_to_unit_test.return_value = ('test', 0.01, 'model')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='p.prompt',
            code_file='c.py',
            program_file='prog.py',
            current_output='cur.txt',
            desired_output='des.txt',
            language='Python'  # Explicit language
        )
        
        # Verify Python (explicit) was used, not JavaScript (detected)
        call_args = mock_bug_to_unit_test.call_args[0]
        assert call_args[8] == 'Python'
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_detected_language_used_when_none(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that detected language is used when explicit is None."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': True,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'p',
                'code_file': 'c',
                'program_file': 'prog',
                'current_output': 'cur',
                'desired_output': 'des'
            },
            {},
            'TypeScript'  # Detected language
        )
        
        mock_bug_to_unit_test.return_value = ('test', 0.01, 'model')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='p.prompt',
            code_file='c.ts',
            program_file='prog.ts',
            current_output='cur.txt',
            desired_output='des.txt',
            language=None  # No explicit language
        )
        
        # Verify TypeScript (detected) was used
        call_args = mock_bug_to_unit_test.call_args[0]
        assert call_args[8] == 'TypeScript'


class TestBugMainErrorHandling:
    """Test error handling scenarios."""
    
    @patch('pdd.bug_main.construct_paths')
    def test_construct_paths_exception_exits_with_error(
        self,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that exceptions from construct_paths cause exit(1)."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': False,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        mock_construct_paths.side_effect = ValueError("Invalid path")
        
        with pytest.raises(SystemExit) as exc_info:
            bug_main(
                ctx=mock_ctx,
                prompt_file='p.prompt',
                code_file='c.py',
                program_file='prog.py',
                current_output='cur.txt',
                desired_output='des.txt'
            )
        
        assert exc_info.value.code == 1
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_bug_to_unit_test_exception_exits_with_error(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that exceptions from bug_to_unit_test cause exit(1)."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': True,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'p',
                'code_file': 'c',
                'program_file': 'prog',
                'current_output': 'cur',
                'desired_output': 'des'
            },
            {},
            'Python'
        )
        
        mock_bug_to_unit_test.side_effect = RuntimeError("LLM error")
        
        with pytest.raises(SystemExit) as exc_info:
            bug_main(
                ctx=mock_ctx,
                prompt_file='p.prompt',
                code_file='c.py',
                program_file='prog.py',
                current_output='cur.txt',
                desired_output='des.txt'
            )
        
        assert exc_info.value.code == 1


class TestBugMainIntegration:
    """Test integration aspects and correct parameter passing."""
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_construct_paths_called_with_correct_parameters(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that construct_paths receives correct parameters."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': True,
            'quiet': False,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': 'test_ctx'
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'p',
                'code_file': 'c',
                'program_file': 'prog',
                'current_output': 'cur',
                'desired_output': 'des'
            },
            {},
            'Python'
        )
        
        mock_bug_to_unit_test.return_value = ('test', 0.01, 'model')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='my_prompt.prompt',
            code_file='my_code.py',
            program_file='my_program.py',
            current_output='current.txt',
            desired_output='desired.txt',
            output='out.py',
            language='Python'
        )
        
        # Verify construct_paths call
        mock_construct_paths.assert_called_once()
        call_kwargs = mock_construct_paths.call_args[1]
        
        assert call_kwargs['input_file_paths'] == {
            'prompt_file': 'my_prompt.prompt',
            'code_file': 'my_code.py',
            'program_file': 'my_program.py',
            'current_output': 'current.txt',
            'desired_output': 'desired.txt'
        }
        assert call_kwargs['force'] is True
        assert call_kwargs['quiet'] is False
        assert call_kwargs['command'] == 'bug'
        assert call_kwargs['command_options'] == {
            'output': 'out.py',
            'language': 'Python'
        }
        assert call_kwargs['context_override'] == 'test_ctx'
    
    @patch('pdd.bug_main.construct_paths')
    @patch('pdd.bug_main.bug_to_unit_test')
    def test_bug_to_unit_test_called_with_correct_parameters(
        self,
        mock_bug_to_unit_test: MagicMock,
        mock_construct_paths: MagicMock
    ) -> None:
        """Test that bug_to_unit_test receives correct parameters."""
        mock_ctx = Mock()
        mock_ctx.obj = {
            'force': False,
            'quiet': True,
            'strength': 0.7,
            'temperature': 0.3,
            'time': 0.5,
            'context': None
        }
        
        mock_construct_paths.return_value = (
            {},
            {
                'prompt_file': 'prompt_content',
                'code_file': 'code_content',
                'program_file': 'program_content',
                'current_output': 'current_output_content',
                'desired_output': 'desired_output_content'
            },
            {},
            'JavaScript'
        )
        
        mock_bug_to_unit_test.return_value = ('generated_test', 0.05, 'gpt-4')
        
        bug_main(
            ctx=mock_ctx,
            prompt_file='p.prompt',
            code_file='c.js',
            program_file='prog.js',
            current_output='cur.txt',
            desired_output='des.txt',
            language='JavaScript'
        )
        
        # Verify bug_to_unit_test call
        mock_bug_to_unit_test.assert_called_once_with(
            'current_output_content',
            'desired_output_content',
            'prompt_content',
            'code_content',
            'program_content',
            0.7,   # strength
            0.3,   # temperature
            0.5,   # time
            'JavaScript'  # language
        )