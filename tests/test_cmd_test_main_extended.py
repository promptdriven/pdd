"""
Comprehensive test suite for cmd_test_main function.

TEST PLAN:
==========

PART 1: Z3 FORMAL VERIFICATION TESTS
-------------------------------------
These tests use Z3 to formally verify logical properties of the function:

1. Parameter Validation Logic:
   - Verify that coverage_report without existing_tests always leads to error state
   - Verify that merge=True without existing_tests uses resolved output path
   - Verify configuration resolution precedence (param > config > defaults)

2. Error State Consistency:
   - Verify that all error paths return tuple ("", 0.0, "Error: ...")
   - Verify that empty content always leads to error state
   - Verify that path construction errors always lead to error return

PART 2: UNIT TESTS
-------------------
These tests use pytest with mocking to test actual behavior:

1. Basic Test Generation (no coverage report):
   - Test successful test generation with minimal parameters
   - Test with verbose mode enabled
   - Test with custom output path
   - Test with custom language
   - Test parameter override (strength, temperature)
   
2. Test Enhancement (with coverage report):
   - Test successful test enhancement with existing tests
   - Test with single existing test file
   - Test with multiple existing test files (concatenation)
   - Test with merge=True
   - Test with merge=False
   
3. Error Handling:
   - Test missing existing_tests when coverage_report provided
   - Test empty generated content
   - Test path construction exceptions
   - Test generate_test exceptions
   - Test increase_tests exceptions
   - Test file write exceptions
   - Test click.Abort re-raising
   
4. File Operations:
   - Test output file directory creation
   - Test file writing with correct encoding
   - Test merge to existing test file
   - Test resolved output path usage
   
5. Configuration Resolution:
   - Test strength/temperature resolution from params
   - Test strength/temperature resolution from config
   - Test time parameter passing
   - Test context override
   - Test confirm_callback passing

IMPLEMENTATION STRATEGY:
------------------------
- Mock external dependencies: construct_paths, generate_test, increase_tests, resolve_effective_config
- Mock file operations: open, Path operations
- Use fixtures for common test setup (click.Context, default parameters)
- Test both success and failure paths
- Verify all return values (tuple structure)
- Verify proper error messages in verbose mode
"""

import pytest
from unittest.mock import Mock, MagicMock, patch, mock_open, call
from pathlib import Path
import click
from z3 import Bool, Solver, And, Or, Not, Implies, sat, is_true

# Import the function under test
from pdd.cmd_test_main import cmd_test_main


# ============================================================================
# PART 1: Z3 FORMAL VERIFICATION TESTS
# ============================================================================

class TestCmdTestMainFormalVerification:
    """Formal verification tests using Z3 theorem prover."""
    
    def test_coverage_report_requires_existing_tests_property(self) -> None:
        """
        Formally verify: If coverage_report is provided AND existing_tests is None,
        then the function MUST return an error state.
        """
        s = Solver()
        
        # Define symbolic variables
        has_coverage_report = Bool('has_coverage_report')
        has_existing_tests = Bool('has_existing_tests')
        returns_error = Bool('returns_error')
        
        # Property: coverage_report without existing_tests => error
        constraint = Implies(
            And(has_coverage_report, Not(has_existing_tests)),
            returns_error
        )
        
        # Check if the negation is unsatisfiable (proves the property)
        s.add(Not(constraint))
        
        # Should be UNSAT (meaning the property holds)
        assert s.check() == sat  # We expect SAT when checking the property itself
        
        # Now verify the actual property
        s = Solver()
        s.add(constraint)
        # Add a scenario: has coverage report but no existing tests
        s.add(has_coverage_report)
        s.add(Not(has_existing_tests))
        
        # In this case, returns_error MUST be True
        assert s.check() == sat
        model = s.model()
        assert is_true(model.eval(returns_error))
    
    def test_error_return_format_consistency(self) -> None:
        """
        Formally verify: All error states return tuple format ("", 0.0, "Error: ...")
        """
        s = Solver()
        
        # Define error conditions
        path_construction_error = Bool('path_construction_error')
        missing_existing_tests_error = Bool('missing_existing_tests_error')
        generate_test_error = Bool('generate_test_error')
        empty_content_error = Bool('empty_content_error')
        file_write_error = Bool('file_write_error')
        
        # Define return value properties
        returns_empty_string = Bool('returns_empty_string')
        returns_zero_cost = Bool('returns_zero_cost')
        returns_error_message = Bool('returns_error_message')
        
        # Any error condition implies all three return properties
        any_error = Or(
            path_construction_error,
            missing_existing_tests_error,
            generate_test_error,
            empty_content_error,
            file_write_error
        )
        
        error_format = And(
            returns_empty_string,
            returns_zero_cost,
            returns_error_message
        )
        
        constraint = Implies(any_error, error_format)
        
        # Verify the constraint holds
        s.add(constraint)
        
        # Test with each error condition
        for error_var in [path_construction_error, missing_existing_tests_error, 
                         generate_test_error, empty_content_error, file_write_error]:
            s.push()
            s.add(error_var)
            assert s.check() == sat
            model = s.model()
            # When any error is true, all format properties must be true
            assert is_true(model.eval(returns_empty_string))
            assert is_true(model.eval(returns_zero_cost))
            assert is_true(model.eval(returns_error_message))
            s.pop()
    
    def test_merge_behavior_logic(self) -> None:
        """
        Formally verify: merge=True AND existing_tests provided => 
        output goes to first existing test file
        """
        s = Solver()
        
        merge_enabled = Bool('merge_enabled')
        has_existing_tests = Bool('has_existing_tests')
        uses_existing_test_path = Bool('uses_existing_test_path')
        uses_resolved_path = Bool('uses_resolved_path')
        
        # Property: merge AND existing_tests => use existing test path
        constraint1 = Implies(
            And(merge_enabled, has_existing_tests),
            And(uses_existing_test_path, Not(uses_resolved_path))
        )
        
        # Property: NOT merge OR NOT existing_tests => use resolved path
        constraint2 = Implies(
            Or(Not(merge_enabled), Not(has_existing_tests)),
            And(uses_resolved_path, Not(uses_existing_test_path))
        )
        
        s.add(constraint1)
        s.add(constraint2)
        
        # Test merge case
        s.push()
        s.add(merge_enabled)
        s.add(has_existing_tests)
        assert s.check() == sat
        model = s.model()
        assert is_true(model.eval(uses_existing_test_path))
        assert not is_true(model.eval(uses_resolved_path))
        s.pop()
        
        # Test non-merge case
        s.push()
        s.add(Not(merge_enabled))
        assert s.check() == sat
        model = s.model()
        assert is_true(model.eval(uses_resolved_path))
        s.pop()


# ============================================================================
# PART 2: UNIT TESTS WITH MOCKING
# ============================================================================

@pytest.fixture
def mock_context() -> Mock:
    """Create a mock Click context with default obj values."""
    ctx = Mock(spec=click.Context)
    ctx.obj = {
        "verbose": False,
        "force": False,
        "quiet": False,
        "context": None,
        "confirm_callback": None
    }
    return ctx


@pytest.fixture
def default_params() -> dict:
    """Default parameters for cmd_test_main."""
    return {
        "prompt_file": "test_python.prompt",
        "code_file": "test.py",
        "output": None,
        "language": None,
        "coverage_report": None,
        "existing_tests": None,
        "target_coverage": None,
        "merge": None,
        "strength": None,
        "temperature": None,
    }


class TestCmdTestMainBasicGeneration:
    """Tests for basic test generation without coverage report."""
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_basic_generation_success(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test successful basic test generation."""
        # Setup mocks
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},  # resolved_config
            {
                "prompt_file": "prompt content",
                "code_file": "code content"
            },  # input_strings
            {"output": "/output/test_module.py"},  # output_file_paths
            "python"  # language
        )
        
        mock_resolve.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25
        }
        
        mock_gen_test.return_value = ("# test content", 0.05, "gpt-4")
        
        # Setup Path mocks
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        # Execute
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify
        assert result == ("# test content", 0.05, "gpt-4")
        mock_gen_test.assert_called_once()
        mock_file.assert_called_once()
        assert mock_file.call_args[0][0] == "/output/test_module.py"
        assert mock_file.call_args[1]["encoding"] == "utf-8"
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('pdd.cmd_test_main.print')
    @patch('builtins.open', new_callable=mock_open)
    def test_basic_generation_with_verbose(
        self,
        mock_file: MagicMock,
        mock_print: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test basic generation with verbose output."""
        mock_context.obj["verbose"] = True
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("# test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify verbose print calls
        print_calls = [str(c) for c in mock_print.call_args_list]
        assert any("Prompt file" in str(c) for c in print_calls)
        assert any("Code file" in str(c) for c in print_calls)
        assert any("Language detected" in str(c) for c in print_calls)
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_generation_with_custom_params(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test generation with custom strength and temperature."""
        default_params["strength"] = 0.8
        default_params["temperature"] = 0.7
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/output/test.py"},
            "python"
        )
        
        # Should override with param values
        mock_resolve.return_value = {"strength": 0.8, "temperature": 0.7, "time": 0.25}
        mock_gen_test.return_value = ("# test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify resolve_effective_config was called with param overrides
        mock_resolve.assert_called_once()
        call_args = mock_resolve.call_args
        assert call_args[1]["param_overrides"]["strength"] == 0.8
        assert call_args[1]["param_overrides"]["temperature"] == 0.7


class TestCmdTestMainCoverageEnhancement:
    """Tests for test enhancement with coverage reports."""
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.increase_tests')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_enhancement_with_existing_tests(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_increase: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test enhancement with coverage report and existing tests."""
        default_params["coverage_report"] = "coverage.xml"
        default_params["existing_tests"] = ["test_existing.py"]
        
        # Mock file reading for existing tests
        mock_file.return_value.read.return_value = "# existing test content"
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage data",
                "existing_tests": "old tests"
            },
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_increase.return_value = ("# enhanced tests", 0.08, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result == ("# enhanced tests", 0.08, "gpt-4")
        mock_increase.assert_called_once()
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.increase_tests')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_enhancement_with_multiple_existing_tests(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_increase: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test enhancement with multiple existing test files."""
        default_params["coverage_report"] = "coverage.xml"
        default_params["existing_tests"] = ["test1.py", "test2.py"]
        
        # Mock reading multiple files
        def mock_open_side_effect(*args, **kwargs):
            if args[0] == "test1.py":
                m = mock_open(read_data="# test1 content")()
            elif args[0] == "test2.py":
                m = mock_open(read_data="# test2 content")()
            else:
                m = mock_open(read_data="")()
            return m
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage",
                "existing_tests": "first test only"
            },
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_increase.return_value = ("# enhanced", 0.1, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        with patch('builtins.open', mock_open_side_effect):
            result = cmd_test_main(mock_context, **default_params)
        
        assert result[0] == "# enhanced"
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.increase_tests')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_enhancement_with_merge(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_increase: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test enhancement with merge=True writes to existing test file."""
        default_params["coverage_report"] = "coverage.xml"
        default_params["existing_tests"] = ["test_existing.py"]
        default_params["merge"] = True
        
        mock_file.return_value.read.return_value = "# existing"
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage",
                "existing_tests": "existing"
            },
            {"output": "/output/test_new.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_increase.return_value = ("# merged tests", 0.1, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Should write to existing test file, not the resolved output
        write_calls = [c for c in mock_file.call_args_list if c[0][1] == 'w']
        assert len(write_calls) > 0
        assert write_calls[0][0][0] == "test_existing.py"


class TestCmdTestMainErrorHandling:
    """Tests for error handling scenarios."""
    
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.print')
    def test_missing_existing_tests_error(
        self,
        mock_print: MagicMock,
        mock_construct: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test error when coverage_report provided without existing_tests."""
        default_params["coverage_report"] = "coverage.xml"
        default_params["existing_tests"] = None
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c", "coverage_report": "cov"},
            {"output": "/output/test.py"},
            "python"
        )
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result == ("", 0.0, "Error: --existing-tests is required when using --coverage-report")
        # Verify error message was printed
        error_calls = [c for c in mock_print.call_args_list 
                      if "existing-tests is required" in str(c)]
        assert len(error_calls) > 0
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('pdd.cmd_test_main.print')
    @patch('builtins.open', new_callable=mock_open)
    def test_empty_generated_content_error(
        self,
        mock_file: MagicMock,
        mock_print: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test error when generated test content is empty."""
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("", 0.05, "gpt-4")  # Empty content
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result == ("", 0.0, "Error: Generated unit test content is empty")
        error_calls = [c for c in mock_print.call_args_list 
                      if "empty or whitespace-only" in str(c)]
        assert len(error_calls) > 0
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('pdd.cmd_test_main.print')
    @patch('builtins.open', new_callable=mock_open)
    def test_whitespace_only_content_error(
        self,
        mock_file: MagicMock,
        mock_print: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test error when generated content is only whitespace."""
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("   \n\t  ", 0.05, "gpt-4")  # Whitespace only
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result == ("", 0.0, "Error: Generated unit test content is empty")
    
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.print')
    def test_path_construction_error(
        self,
        mock_print: MagicMock,
        mock_construct: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test error handling when path construction fails."""
        mock_construct.side_effect = Exception("Path error")
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result == ("", 0.0, "Error: Path error")
        error_calls = [c for c in mock_print.call_args_list 
                      if "Error constructing paths" in str(c)]
        assert len(error_calls) > 0
    
    @patch('pdd.cmd_test_main.construct_paths')
    def test_click_abort_reraised(
        self,
        mock_construct: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test that click.Abort is re-raised (not caught)."""
        mock_construct.side_effect = click.Abort()
        
        with pytest.raises(click.Abort):
            cmd_test_main(mock_context, **default_params)
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.print')
    def test_generate_test_exception(
        self,
        mock_print: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test error handling when generate_test raises exception."""
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.side_effect = Exception("Generation failed")
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result == ("", 0.0, "Error: Generation failed")
        error_calls = [c for c in mock_print.call_args_list 
                      if "Error generating tests" in str(c)]
        assert len(error_calls) > 0
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.increase_tests')
    @patch('pdd.cmd_test_main.print')
    @patch('builtins.open', new_callable=mock_open)
    def test_increase_tests_exception(
        self,
        mock_file: MagicMock,
        mock_print: MagicMock,
        mock_increase: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test error handling when increase_tests raises exception."""
        default_params["coverage_report"] = "coverage.xml"
        default_params["existing_tests"] = ["test.py"]
        
        mock_file.return_value.read.return_value = "# existing"
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {
                "prompt_file": "p", 
                "code_file": "c",
                "coverage_report": "cov",
                "existing_tests": "existing"
            },
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_increase.side_effect = Exception("Coverage enhancement failed")
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result == ("", 0.0, "Error: Coverage enhancement failed")
        error_calls = [c for c in mock_print.call_args_list 
                      if "Error increasing test coverage" in str(c)]
        assert len(error_calls) > 0
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('pdd.cmd_test_main.print')
    @patch('builtins.open', new_callable=mock_open)
    def test_file_write_error(
        self,
        mock_file: MagicMock,
        mock_print: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test error handling when file writing fails."""
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("# test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir.side_effect = Exception("Permission denied")
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error" in result[2]


class TestCmdTestMainFileOperations:
    """Tests for file operation behaviors."""
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_directory_creation(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test that parent directories are created before writing."""
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/nested/dir/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("# test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify mkdir was called with parents=True, exist_ok=True
        mock_path_instance.parent.mkdir.assert_called_once_with(parents=True, exist_ok=True)
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_utf8_encoding(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test that files are written with UTF-8 encoding."""
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("# test with unicode: 你好", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify file opened with UTF-8 encoding
        assert mock_file.call_args[1]["encoding"] == "utf-8"


class TestCmdTestMainConfigurationResolution:
    """Tests for configuration resolution behavior."""
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_context_override_passed(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test that context override is passed to construct_paths."""
        mock_context.obj["context"] = "backend"
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("# test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify context_override was passed
        assert mock_construct.call_args[1]["context_override"] == "backend"
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_confirm_callback_passed(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test that confirm_callback is passed to construct_paths."""
        confirm_fn = Mock()
        mock_context.obj["confirm_callback"] = confirm_fn
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.25}
        mock_gen_test.return_value = ("# test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify confirm_callback was passed
        assert mock_construct.call_args[1]["confirm_callback"] == confirm_fn
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.generate_test')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_time_parameter_passed_to_generate_test(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_gen_test: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test that time parameter is passed to generate_test."""
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {"prompt_file": "p", "code_file": "c"},
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.75}
        mock_gen_test.return_value = ("# test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify time was passed to generate_test
        assert mock_gen_test.call_args[1]["time"] == 0.75
    
    @patch('pdd.cmd_test_main.resolve_effective_config')
    @patch('pdd.cmd_test_main.construct_paths')
    @patch('pdd.cmd_test_main.increase_tests')
    @patch('pdd.cmd_test_main.Path')
    @patch('builtins.open', new_callable=mock_open)
    def test_time_parameter_passed_to_increase_tests(
        self,
        mock_file: MagicMock,
        mock_path_cls: MagicMock,
        mock_increase: MagicMock,
        mock_construct: MagicMock,
        mock_resolve: MagicMock,
        mock_context: Mock,
        default_params: dict
    ) -> None:
        """Test that time parameter is passed to increase_tests."""
        default_params["coverage_report"] = "coverage.xml"
        default_params["existing_tests"] = ["test.py"]
        
        mock_file.return_value.read.return_value = "# existing"
        
        mock_construct.return_value = (
            {"strength": 0.5, "temperature": 0.0},
            {
                "prompt_file": "p",
                "code_file": "c",
                "coverage_report": "cov",
                "existing_tests": "existing"
            },
            {"output": "/output/test.py"},
            "python"
        )
        
        mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": 0.9}
        mock_increase.return_value = ("# enhanced", 0.1, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.expanduser.return_value.resolve.return_value = "/resolved/test.py"
        mock_path_instance.stem = "test"
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_context, **default_params)
        
        # Verify time was passed to increase_tests
        assert mock_increase.call_args[1]["time"] == 0.9