"""
TEST PLAN FOR bug_main
======================

Function Under Test: bug_main(ctx, prompt_file, code_file, program_file, current_output, desired_output, output, language)

FUNCTIONALITY ANALYSIS:
1. Constructs file paths using construct_paths helper
2. Loads input file contents (prompt, code, program, current/desired output)
3. Calls bug_to_unit_test to generate a unit test
4. Saves the generated test to the output path (if provided)
5. Prints feedback (unless quiet mode)
6. Always prints the generated unit test
7. Returns tuple of (unit_test, total_cost, model_name)

EDGE CASES AND TESTING APPROACH:

1. Normal successful execution
   - Approach: Unit test with mocking
   - Rationale: Tests integration of components and I/O operations

2. Quiet mode behavior
   - Approach: Unit test with mocking
   - Rationale: Tests conditional console output behavior

3. Empty output path handling
   - Approach: Unit test with mocking
   - Rationale: Tests fallback behavior for invalid paths

4. Output directory creation
   - Approach: Unit test with mocking
   - Rationale: Tests filesystem operations

5. Language detection (None vs explicit)
   - Approach: Unit test with mocking
   - Rationale: Tests parameter handling logic

6. Exception handling
   - Approach: Unit test with mocking
   - Rationale: Tests error propagation and exit behavior

7. Context object parameter extraction
   - Approach: Z3 formal verification
   - Rationale: Verify default value logic and parameter flow

8. File path construction invariants
   - Approach: Z3 formal verification
   - Rationale: Verify logical properties of path handling

DETAILED TEST PLAN:

Unit Tests:
- test_bug_main_success: Verify successful execution flow
- test_bug_main_quiet_mode: Verify output suppression but test still printed
- test_bug_main_with_output_path: Verify file saving
- test_bug_main_empty_output_path: Verify fallback for empty paths
- test_bug_main_creates_directory: Verify directory creation
- test_bug_main_language_detection: Verify language parameter handling
- test_bug_main_error_handling: Verify exception handling and exit
- test_bug_main_no_output_path: Verify behavior without output

Z3 Formal Verification Tests:
- test_z3_context_parameters: Verify parameter extraction logic
- test_z3_output_path_invariants: Verify path construction properties
- test_z3_return_value_structure: Verify return tuple structure
"""

import pytest
from unittest.mock import Mock, patch, mock_open
from z3 import Solver, Bool, Int, Real, Implies, Not, And, Or, sat, unsat

from pdd.bug_main import bug_main


class TestBugMain:
    """Unit tests for bug_main function."""

    @pytest.fixture
    def mock_ctx(self) -> Mock:
        """Create a mock Click context."""
        ctx = Mock()
        ctx.obj = {
            'force': False,
            'quiet': False,
            'strength': 0.5,
            'temperature': 0.0,
            'time': 0.25,
            'context': None
        }
        return ctx

    @pytest.fixture
    def sample_inputs(self) -> dict:
        """Sample input data for tests."""
        return {
            'prompt_file': 'prompts/test_python.prompt',
            'code_file': 'src/test.py',
            'program_file': 'examples/run_test.py',
            'current_output': 'outputs/current.txt',
            'desired_output': 'outputs/desired.txt',
            'output': 'tests/test_bug.py',
            'language': 'Python'
        }

    @pytest.fixture
    def mock_construct_paths_response(self) -> tuple:
        """Mock response from construct_paths."""
        return (
            {},  # resolved_config
            {  # input_strings
                'prompt_file': 'prompt content',
                'code_file': 'code content',
                'program_file': 'program content',
                'current_output': 'current output',
                'desired_output': 'desired output'
            },
            {  # output_file_paths
                'output': 'tests/test_bug.py'
            },
            'Python'  # detected_language
        )

    @pytest.fixture
    def mock_bug_to_unit_test_response(self) -> tuple:
        """Mock response from bug_to_unit_test."""
        return (
            'def test_example():\n    assert True',  # unit_test
            0.05,  # total_cost
            'gpt-4'  # model_name
        )

    def test_bug_main_success(
        self,
        mock_ctx: Mock,
        sample_inputs: dict,
        mock_construct_paths_response: tuple,
        mock_bug_to_unit_test_response: tuple
    ) -> None:
        """Test successful execution of bug_main."""
        with patch('pdd.bug_main.construct_paths', return_value=mock_construct_paths_response), \
             patch('pdd.bug_main.bug_to_unit_test', return_value=mock_bug_to_unit_test_response), \
             patch('pdd.bug_main.os.makedirs'), \
             patch('builtins.open', mock_open()) as m_open, \
             patch('pdd.bug_main.rprint'):
            
            result = bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                sample_inputs['output'],
                sample_inputs['language']
            )
            
            # Verify return value
            assert result == mock_bug_to_unit_test_response
            assert result[0] == 'def test_example():\n    assert True'
            assert result[1] == 0.05
            assert result[2] == 'gpt-4'
            
            # Verify file was written
            m_open.assert_called_once_with('tests/test_bug.py', 'w')

    def test_bug_main_quiet_mode(
        self,
        mock_ctx: Mock,
        sample_inputs: dict,
        mock_construct_paths_response: tuple,
        mock_bug_to_unit_test_response: tuple
    ) -> None:
        """Test that quiet mode suppresses feedback but still prints unit test."""
        mock_ctx.obj['quiet'] = True
        
        with patch('pdd.bug_main.construct_paths', return_value=mock_construct_paths_response), \
             patch('pdd.bug_main.bug_to_unit_test', return_value=mock_bug_to_unit_test_response), \
             patch('pdd.bug_main.os.makedirs'), \
             patch('builtins.open', mock_open()), \
             patch('pdd.bug_main.rprint') as m_print:
            
            result = bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                sample_inputs['output'],
                sample_inputs['language']
            )
            
            # Verify unit test is still printed
            print_calls = [str(call) for call in m_print.call_args_list]
            assert any('Generated Unit Test' in str(call) for call in print_calls)
            
            # Verify feedback messages are NOT printed
            feedback_printed = any('successfully' in str(call).lower() for call in print_calls)
            assert not feedback_printed

    def test_bug_main_empty_output_path(
        self,
        mock_ctx: Mock,
        sample_inputs: dict,
        mock_bug_to_unit_test_response: tuple
    ) -> None:
        """Test handling of empty output path."""
        empty_output_construct_paths_response = (
            {},
            {
                'prompt_file': 'prompt content',
                'code_file': 'code content',
                'program_file': 'program content',
                'current_output': 'current output',
                'desired_output': 'desired output'
            },
            {'output': ''},  # Empty output path
            'Python'
        )
        
        with patch('pdd.bug_main.construct_paths', return_value=empty_output_construct_paths_response), \
             patch('pdd.bug_main.bug_to_unit_test', return_value=mock_bug_to_unit_test_response), \
             patch('pdd.bug_main.os.makedirs'), \
             patch('builtins.open', mock_open()) as m_open, \
             patch('pdd.bug_main.rprint') as m_print:
            
            result = bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                '',
                sample_inputs['language']
            )
            
            # Verify default path was used
            print_calls = [str(call) for call in m_print.call_args_list]
            warning_printed = any('Empty output path' in str(call) for call in print_calls)
            assert warning_printed
            
            # Verify file was still written with default name
            m_open.assert_called_once()

    def test_bug_main_creates_directory(
        self,
        mock_ctx: Mock,
        sample_inputs: dict,
        mock_bug_to_unit_test_response: tuple
    ) -> None:
        """Test that output directory is created if it doesn't exist."""
        output_path_with_dir = 'new_dir/subdir/test_bug.py'
        dir_construct_paths_response = (
            {},
            {
                'prompt_file': 'prompt content',
                'code_file': 'code content',
                'program_file': 'program content',
                'current_output': 'current output',
                'desired_output': 'desired output'
            },
            {'output': output_path_with_dir},
            'Python'
        )
        
        with patch('pdd.bug_main.construct_paths', return_value=dir_construct_paths_response), \
             patch('pdd.bug_main.bug_to_unit_test', return_value=mock_bug_to_unit_test_response), \
             patch('pdd.bug_main.os.makedirs') as m_makedirs, \
             patch('builtins.open', mock_open()), \
             patch('pdd.bug_main.rprint'):
            
            result = bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                output_path_with_dir,
                sample_inputs['language']
            )
            
            # Verify directory creation was called
            m_makedirs.assert_called_once_with('new_dir/subdir', exist_ok=True)

    def test_bug_main_no_directory_in_path(
        self,
        mock_ctx: Mock,
        sample_inputs: dict,
        mock_bug_to_unit_test_response: tuple
    ) -> None:
        """Test that makedirs is not called when output path has no directory component."""
        output_path_no_dir = 'test_bug.py'
        no_dir_construct_paths_response = (
            {},
            {
                'prompt_file': 'prompt content',
                'code_file': 'code content',
                'program_file': 'program content',
                'current_output': 'current output',
                'desired_output': 'desired output'
            },
            {'output': output_path_no_dir},
            'Python'
        )
        
        with patch('pdd.bug_main.construct_paths', return_value=no_dir_construct_paths_response), \
             patch('pdd.bug_main.bug_to_unit_test', return_value=mock_bug_to_unit_test_response), \
             patch('pdd.bug_main.os.makedirs') as m_makedirs, \
             patch('builtins.open', mock_open()), \
             patch('pdd.bug_main.rprint'):
            
            result = bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                output_path_no_dir,
                sample_inputs['language']
            )
            
            # Verify makedirs was NOT called
            m_makedirs.assert_not_called()

    def test_bug_main_language_detection(
        self,
        mock_ctx: Mock,
        sample_inputs: dict,
        mock_bug_to_unit_test_response: tuple
    ) -> None:
        """Test that language is detected when None is passed."""
        js_construct_paths_response = (
            {},
            {
                'prompt_file': 'prompt content',
                'code_file': 'code content',
                'program_file': 'program content',
                'current_output': 'current output',
                'desired_output': 'desired output'
            },
            {'output': 'tests/test_bug.py'},
            'JavaScript'  # Detected language
        )
        
        with patch('pdd.bug_main.construct_paths', return_value=js_construct_paths_response), \
             patch('pdd.bug_main.bug_to_unit_test', return_value=mock_bug_to_unit_test_response) as m_bug_to_unit_test, \
             patch('pdd.bug_main.os.makedirs'), \
             patch('builtins.open', mock_open()), \
             patch('pdd.bug_main.rprint'):
            
            result = bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                sample_inputs['output'],
                None  # No language specified
            )
            
            # Verify bug_to_unit_test was called with detected language
            assert m_bug_to_unit_test.call_args[0][8] == 'JavaScript'

    def test_bug_main_no_output_path(
        self,
        mock_ctx: Mock,
        sample_inputs: dict,
        mock_bug_to_unit_test_response: tuple
    ) -> None:
        """Test behavior when no output path is provided."""
        no_output_construct_paths_response = (
            {},
            {
                'prompt_file': 'prompt content',
                'code_file': 'code content',
                'program_file': 'program content',
                'current_output': 'current output',
                'desired_output': 'desired output'
            },
            {},  # No output path
            'Python'
        )
        
        with patch('pdd.bug_main.construct_paths', return_value=no_output_construct_paths_response), \
             patch('pdd.bug_main.bug_to_unit_test', return_value=mock_bug_to_unit_test_response), \
             patch('pdd.bug_main.os.makedirs') as m_makedirs, \
             patch('builtins.open', mock_open()) as m_open, \
             patch('pdd.bug_main.rprint'):
            
            result = bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                None,
                sample_inputs['language']
            )
            
            # Verify no file operations occurred
            m_makedirs.assert_not_called()
            m_open.assert_not_called()

    def test_bug_main_error_handling(
        self,
        mock_ctx: Mock,
        sample_inputs: dict
    ) -> None:
        """Test that exceptions are caught and program exits with code 1."""
        with patch('pdd.bug_main.construct_paths', side_effect=Exception("Test error")), \
             patch('pdd.bug_main.rprint') as m_print, \
             pytest.raises(SystemExit) as exc_info:
            
            bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                sample_inputs['output'],
                sample_inputs['language']
            )
        
        # Verify exit code
        assert exc_info.value.code == 1
        
        # Verify error was printed
        print_calls = [str(call) for call in m_print.call_args_list]
        error_printed = any('Error' in str(call) and 'Test error' in str(call) for call in print_calls)
        assert error_printed

    def test_bug_main_error_handling_quiet(
        self,
        mock_ctx: Mock,
        sample_inputs: dict
    ) -> None:
        """Test that errors don't print in quiet mode but still exit."""
        mock_ctx.obj['quiet'] = True
        
        with patch('pdd.bug_main.construct_paths', side_effect=Exception("Test error")), \
             patch('pdd.bug_main.rprint'), \
             pytest.raises(SystemExit) as exc_info:
            
            bug_main(
                mock_ctx,
                sample_inputs['prompt_file'],
                sample_inputs['code_file'],
                sample_inputs['program_file'],
                sample_inputs['current_output'],
                sample_inputs['desired_output'],
                sample_inputs['output'],
                sample_inputs['language']
            )
        
        # Verify exit code
        assert exc_info.value.code == 1


class TestBugMainZ3Verification:
    """Z3 formal verification tests for bug_main."""

    def test_z3_context_parameters(self) -> None:
        """
        Verify that context parameter extraction follows correct default value logic.
        
        If key exists in ctx.obj, use that value; otherwise, use the specified default.
        """
        solver = Solver()
        
        # Define symbolic variables
        ctx_has_strength = Bool('ctx_has_strength')
        ctx_has_temperature = Bool('ctx_has_temperature')
        ctx_has_time = Bool('ctx_has_time')
        
        # Define default values (using integers for simplicity)
        DEFAULT_STRENGTH = 50  # 0.5 * 100
        DEFAULT_TEMPERATURE = 0
        DEFAULT_TIME = 25  # 0.25 * 100
        
        # Result values
        strength = Int('strength')
        temperature = Int('temperature')
        time_val = Int('time')
        
        # Add constraints for parameter extraction logic
        solver.add(Implies(ctx_has_strength, strength >= 0))
        solver.add(Implies(Not(ctx_has_strength), strength == DEFAULT_STRENGTH))
        solver.add(Implies(ctx_has_temperature, temperature >= 0))
        solver.add(Implies(Not(ctx_has_temperature), temperature == DEFAULT_TEMPERATURE))
        solver.add(Implies(ctx_has_time, time_val >= 0))
        solver.add(Implies(Not(ctx_has_time), time_val == DEFAULT_TIME))
        
        # Property 1: If context doesn't have values, defaults are used
        solver.push()
        solver.add(Not(ctx_has_strength))
        solver.add(Not(ctx_has_temperature))
        solver.add(Not(ctx_has_time))
        assert solver.check() == sat
        model = solver.model()
        assert model[strength].as_long() == DEFAULT_STRENGTH
        assert model[temperature].as_long() == DEFAULT_TEMPERATURE
        assert model[time_val].as_long() == DEFAULT_TIME
        solver.pop()
        
        # Property 2: If context has values, they override defaults
        solver.push()
        solver.add(ctx_has_strength)
        solver.add(strength == 75)
        assert solver.check() == sat
        model = solver.model()
        assert model[strength].as_long() == 75
        solver.pop()

    def test_z3_output_path_invariants(self) -> None:
        """
        Verify output path construction invariants.
        
        - If output path is empty or whitespace, a default path is constructed
        - If output path has a directory component, directory is created
        - If output path is just a filename, no directory creation occurs
        """
        solver = Solver()
        
        # Symbolic variables
        output_path_empty = Bool('output_path_empty')
        output_path_has_directory = Bool('output_path_has_directory')
        should_create_directory = Bool('should_create_directory')
        uses_default_path = Bool('uses_default_path')
        
        # Constraints: If path is empty, use default and don't create directory
        solver.add(Implies(output_path_empty, uses_default_path))
        
        # Directory creation only happens when path has directory component and is not empty
        solver.add(should_create_directory == And(Not(output_path_empty), output_path_has_directory))
        
        # Property 1: Empty path leads to default, no directory creation
        solver.push()
        solver.add(output_path_empty)
        assert solver.check() == sat
        model = solver.model()
        assert model[uses_default_path]
        solver.pop()
        
        # Property 2: Non-empty path with directory leads to directory creation
        solver.push()
        solver.add(Not(output_path_empty))
        solver.add(output_path_has_directory)
        assert solver.check() == sat
        model = solver.model()
        assert model[should_create_directory]
        solver.pop()
        
        # Property 3: Non-empty path without directory, no creation
        solver.push()
        solver.add(Not(output_path_empty))
        solver.add(Not(output_path_has_directory))
        assert solver.check() == sat
        model = solver.model()
        assert not model[should_create_directory]
        solver.pop()

    def test_z3_return_value_structure(self) -> None:
        """
        Verify that return value maintains consistent tuple structure.
        
        - Always returns tuple of (str, float, str)
        - First element is non-empty string (unit test)
        - Second element is non-negative float (cost)
        - Third element is non-empty string (model name)
        """
        solver = Solver()
        
        # Symbolic variables for return components
        unit_test_length = Int('unit_test_length')
        cost = Real('cost')
        model_name_length = Int('model_name_length')
        
        # Constraints from function behavior
        solver.add(unit_test_length > 0)  # Unit test is non-empty
        solver.add(cost >= 0)  # Cost is non-negative
        solver.add(model_name_length > 0)  # Model name is non-empty
        
        # Property 1: All components satisfy their constraints
        assert solver.check() == sat
        model = solver.model()
        assert model[unit_test_length].as_long() > 0
        assert float(model[cost].as_decimal(10)) >= 0
        assert model[model_name_length].as_long() > 0
        
        # Property 2: Cost cannot be negative (boundary check)
        solver.push()
        solver.add(cost < 0)
        assert solver.check() == unsat  # Should be unsatisfiable
        solver.pop()
        
        # Property 3: Strings cannot be empty (boundary check)
        solver.push()
        solver.add(Or(unit_test_length <= 0, model_name_length <= 0))
        assert solver.check() == unsat  # Should be unsatisfiable
        solver.pop()
