"""
Test suite for cmd_test_main function.

DETAILED TEST PLAN
==================

This test suite validates the cmd_test_main function which serves as the CLI wrapper
for generating or enhancing unit tests. The function has complex behavior involving
file I/O, external API calls, configuration resolution, and error handling.

Testing Strategy:
-----------------
We use UNIT TESTS exclusively because:
1. Z3 formal verification is NOT suitable for this code because:
   - The code primarily performs I/O operations and API calls
   - It doesn't contain mathematical properties or constraints to verify
   - It doesn't implement algorithms that can be formally verified
   - The behavior depends on external systems (file system, LLM APIs)
   
2. Unit tests ARE suitable because:
   - We can mock external dependencies (construct_paths, generate_test, increase_tests)
   - We can test error handling comprehensively
   - We can verify file I/O operations with temporary files
   - We can validate all code paths and edge cases

Test Categories:
----------------

1. BASIC GENERATION MODE (no coverage report):
   - Successful test generation with default parameters
   - Test generation with explicit output path
   - Test generation with language override
   - Test generation with verbose mode
   - Parameter resolution (strength, temperature, time)
   - File path resolution for prompt parameters (source_file_path, test_file_path, module_name)

2. COVERAGE ENHANCEMENT MODE (with coverage report):
   - Successful test enhancement with single existing test file
   - Test enhancement with multiple existing test files
   - Test enhancement with merge mode
   - Error when existing_tests is missing

3. ERROR HANDLING:
   - construct_paths raises exception -> return error tuple
   - generate_test raises exception -> return error tuple
   - increase_tests raises exception -> return error tuple
   - Empty generated content -> return error tuple
   - File write errors -> return error tuple
   - click.Abort -> re-raise (don't return error tuple)

4. CONFIGURATION RESOLUTION:
   - Strength parameter from CLI overrides context
   - Temperature parameter from CLI overrides context
   - Time parameter from context
   - Context override handling

5. OUTPUT PATH HANDLING:
   - Create parent directories if needed
   - Use resolved output path from construct_paths
   - Merge mode writes to first existing test file
   - UTF-8 encoding for output

6. EDGE CASES:
   - None values for optional parameters
   - Empty strings
   - Whitespace-only generated content
   - Missing output file path

Edge Case Analysis:
-------------------
- File I/O errors: Unit test with mocking (not Z3 - I/O is non-deterministic)
- Empty content validation: Unit test (straightforward condition check)
- Parameter resolution: Unit test with mocking (depends on external config system)
- Multiple file handling: Unit test (list operations, not mathematical)
- Error propagation: Unit test (testing exception handling flow)

Implementation Notes:
--------------------
- Mock external dependencies: construct_paths, resolve_effective_config, generate_test, increase_tests
- Use temporary files/directories for file I/O tests
- Mock ctx.obj to provide required configuration
- Verify all error conditions return proper error tuples
- Verify click.Abort is re-raised (not caught and converted to error tuple)
- Test both verbose and quiet modes
- Verify proper parameter passing to all called functions
"""

import pytest
from pathlib import Path
from unittest.mock import Mock, patch, mock_open, MagicMock
import click

# Import the function under test using the ACTUAL module path
from pdd.cmd_test_main import cmd_test_main


# Fixtures
@pytest.fixture
def mock_ctx():
    """Create a mock Click context with required obj attributes."""
    ctx = Mock(spec=click.Context)
    ctx.obj = {
        "verbose": False,
        "quiet": False,
        "force": False,
        "context": None,
        "confirm_callback": None,
    }
    return ctx


@pytest.fixture
def basic_inputs():
    """Basic input parameters for test generation."""
    return {
        "prompt_file": "test_prompt.prompt",
        "code_file": "test_code.py",
        "output": None,
        "language": None,
        "coverage_report": None,
        "existing_tests": None,
        "target_coverage": None,
        "merge": None,
        "strength": None,
        "temperature": None,
    }


# Test Category 1: BASIC GENERATION MODE
def test_basic_generation_success(mock_ctx, basic_inputs):
    """Test successful test generation without coverage report."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as mock_file, \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        # Setup mocks
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {
                "prompt_file": "prompt content",
                "code_file": "code content",
            },
            {"output": "/tmp/test_output.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("generated test code", 0.05, "gpt-4")
        
        # Setup Path mock
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        # Execute
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify
        assert result == ("generated test code", 0.05, "gpt-4")
        mock_generate_test.assert_called_once()
        mock_file.assert_called_once_with("/tmp/test_output.py", "w", encoding="utf-8")


def test_generation_with_explicit_output(mock_ctx, basic_inputs):
    """Test generation with explicit output path specified."""
    basic_inputs["output"] = "/custom/output/test.py"
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as mock_file, \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/custom/output/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test code", 0.03, "gpt-3.5")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result == ("test code", 0.03, "gpt-3.5")
        mock_file.assert_called_once_with("/custom/output/test.py", "w", encoding="utf-8")


def test_generation_with_language_override(mock_ctx, basic_inputs):
    """Test generation with explicit language parameter."""
    basic_inputs["language"] = "javascript"
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.js"},
            "javascript"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("js test", 0.02, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == "js test"
        # Verify language was passed to generate_test
        call_kwargs = mock_generate_test.call_args[1]
        assert call_kwargs["language"] == "javascript"


def test_generation_with_verbose_mode(mock_ctx, basic_inputs):
    """Test generation with verbose output enabled."""
    mock_ctx.obj["verbose"] = True
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls, \
         patch("pdd.cmd_test_main.print") as mock_print:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify verbose output was printed
        assert mock_print.call_count > 0


def test_parameter_resolution_with_cli_overrides(mock_ctx, basic_inputs):
    """Test that CLI parameters override context configuration."""
    basic_inputs["strength"] = 0.8
    basic_inputs["temperature"] = 0.5
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        # Mock resolve_effective_config to return CLI values
        mock_resolve_config.return_value = {
            "strength": 0.8,  # CLI override
            "temperature": 0.5,  # CLI override
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify resolve_effective_config was called with param_overrides
        mock_resolve_config.assert_called_once()
        call_kwargs = mock_resolve_config.call_args[1]
        assert call_kwargs["param_overrides"]["strength"] == 0.8
        assert call_kwargs["param_overrides"]["temperature"] == 0.5


def test_file_path_parameters_passed_to_generate_test(mock_ctx, basic_inputs):
    """Test that source_file_path, test_file_path, and module_name are correctly passed."""
    basic_inputs["code_file"] = "/home/user/src/my_module.py"
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/home/user/tests/test_my_module.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        # Mock Path to return expected values
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_instance.stem = "my_module"
        mock_path_cls.return_value = mock_path_instance
        
        # Mock expanduser and resolve
        with patch.object(Path, "expanduser") as mock_expanduser, \
             patch.object(Path, "resolve") as mock_resolve:
            mock_expanduser.return_value.resolve.return_value = Path("/home/user/src/my_module.py")
            
            cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify parameters passed to generate_test
        call_kwargs = mock_generate_test.call_args[1]
        assert "source_file_path" in call_kwargs
        assert "test_file_path" in call_kwargs
        assert "module_name" in call_kwargs


# Test Category 2: COVERAGE ENHANCEMENT MODE
def test_coverage_enhancement_with_single_existing_test(mock_ctx, basic_inputs):
    """Test successful test enhancement with coverage report and single existing test."""
    basic_inputs["coverage_report"] = "coverage.xml"
    basic_inputs["existing_tests"] = ["test_existing.py"]
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open(read_data="existing test content")) as mock_file, \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage xml",
                "existing_tests": "existing test content",
            },
            {"output": "/tmp/test_enhanced.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_increase_tests.return_value = ("enhanced tests", 0.08, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result == ("enhanced tests", 0.08, "gpt-4")
        mock_increase_tests.assert_called_once()


def test_coverage_enhancement_with_multiple_existing_tests(mock_ctx, basic_inputs):
    """Test enhancement with multiple existing test files."""
    basic_inputs["coverage_report"] = "coverage.xml"
    basic_inputs["existing_tests"] = ["test1.py", "test2.py", "test3.py"]
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open(read_data="test content")) as mock_file, \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage",
                "existing_tests": "test content",
            },
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_increase_tests.return_value = ("enhanced", 0.1, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == "enhanced"
        # Verify all test files were read and concatenated
        assert mock_file.call_count >= 3  # At least 3 reads + 1 write


def test_coverage_enhancement_with_merge_mode(mock_ctx, basic_inputs):
    """Test that merge mode writes to first existing test file."""
    basic_inputs["coverage_report"] = "coverage.xml"
    basic_inputs["existing_tests"] = ["test_existing.py"]
    basic_inputs["merge"] = True
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open(read_data="test content")) as mock_file, \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage",
                "existing_tests": "test content",
            },
            {"output": "/tmp/test_new.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_increase_tests.return_value = ("merged tests", 0.07, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == "merged tests"
        # Verify write was to existing test file, not new one
        write_call = [call for call in mock_file.mock_calls if 'test_existing.py' in str(call)]
        assert len(write_call) > 0


def test_coverage_enhancement_missing_existing_tests_error(mock_ctx, basic_inputs):
    """Test error when coverage_report provided without existing_tests."""
    basic_inputs["coverage_report"] = "coverage.xml"
    basic_inputs["existing_tests"] = None
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.print"):
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage",
            },
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        # Should return error tuple
        assert result[0] == ""
        assert result[1] == 0.0
        assert "existing-tests is required" in result[2]


# Test Category 3: ERROR HANDLING
def test_construct_paths_error_returns_error_tuple(mock_ctx, basic_inputs):
    """Test that construct_paths exception returns error tuple."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.print"):
        
        mock_construct_paths.side_effect = Exception("Path construction failed")
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error" in result[2]
        assert "Path construction failed" in result[2]


def test_construct_paths_abort_is_reraised(mock_ctx, basic_inputs):
    """Test that click.Abort is re-raised, not caught."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths:
        
        mock_construct_paths.side_effect = click.Abort()
        
        with pytest.raises(click.Abort):
            cmd_test_main(mock_ctx, **basic_inputs)


def test_generate_test_error_returns_error_tuple(mock_ctx, basic_inputs):
    """Test that generate_test exception returns error tuple."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("pdd.cmd_test_main.print"):
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.side_effect = Exception("Generation failed")
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error" in result[2]
        assert "Generation failed" in result[2]


def test_increase_tests_error_returns_error_tuple(mock_ctx, basic_inputs):
    """Test that increase_tests exception returns error tuple."""
    basic_inputs["coverage_report"] = "coverage.xml"
    basic_inputs["existing_tests"] = ["test.py"]
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open(read_data="test")), \
         patch("pdd.cmd_test_main.print"):
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {
                "prompt_file": "prompt",
                "code_file": "code",
                "coverage_report": "coverage",
                "existing_tests": "test",
            },
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_increase_tests.side_effect = Exception("Enhancement failed")
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error" in result[2]
        assert "Enhancement failed" in result[2]


def test_empty_generated_content_returns_error_tuple(mock_ctx, basic_inputs):
    """Test that empty generated test content returns error tuple."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("pdd.cmd_test_main.print"):
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        # Return empty string
        mock_generate_test.return_value = ("", 0.05, "gpt-4")
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "empty" in result[2].lower()


def test_whitespace_only_content_returns_error_tuple(mock_ctx, basic_inputs):
    """Test that whitespace-only generated content returns error tuple."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("pdd.cmd_test_main.print"):
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        # Return whitespace only
        mock_generate_test.return_value = ("   \n\t  \n  ", 0.05, "gpt-4")
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "empty" in result[2].lower()


def test_file_write_error_returns_error_tuple(mock_ctx, basic_inputs):
    """Test that file write errors return error tuple."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open") as mock_file, \
         patch("pdd.cmd_test_main.Path") as mock_path_cls, \
         patch("pdd.cmd_test_main.print"):
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test code", 0.05, "gpt-4")
        
        # Mock file write to raise exception
        mock_file.side_effect = IOError("Permission denied")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error" in result[2]
        assert "Permission denied" in result[2]


# Test Category 4: CONFIGURATION RESOLUTION
def test_context_override_passed_to_construct_paths(mock_ctx, basic_inputs):
    """Test that context override from ctx.obj is passed to construct_paths."""
    mock_ctx.obj["context"] = "backend"
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify context was passed
        call_kwargs = mock_construct_paths.call_args[1]
        assert call_kwargs["context_override"] == "backend"


def test_confirm_callback_passed_to_construct_paths(mock_ctx, basic_inputs):
    """Test that confirm_callback from ctx.obj is passed to construct_paths."""
    mock_callback = Mock()
    mock_ctx.obj["confirm_callback"] = mock_callback
    
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify callback was passed
        call_kwargs = mock_construct_paths.call_args[1]
        assert call_kwargs["confirm_callback"] == mock_callback


# Test Category 5: OUTPUT PATH HANDLING
def test_parent_directory_creation(mock_ctx, basic_inputs):
    """Test that parent directories are created if they don't exist."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/deep/nested/path/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_parent = Mock()
        mock_path_instance.parent = mock_parent
        mock_path_cls.return_value = mock_path_instance
        
        cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify mkdir was called with correct parameters
        mock_parent.mkdir.assert_called_once_with(parents=True, exist_ok=True)


def test_utf8_encoding_used_for_output(mock_ctx, basic_inputs):
    """Test that UTF-8 encoding is used when writing output file."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as mock_file, \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test with unicode: 你好", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        cmd_test_main(mock_ctx, **basic_inputs)
        
        # Verify encoding parameter
        mock_file.assert_called_once_with("/tmp/test.py", "w", encoding="utf-8")


# Test Category 6: EDGE CASES
def test_none_optional_parameters(mock_ctx):
    """Test handling of all None optional parameters."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()), \
         patch("pdd.cmd_test_main.Path") as mock_path_cls:
        
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": "/tmp/test.py"},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        mock_path_instance = Mock()
        mock_path_instance.parent.mkdir = Mock()
        mock_path_cls.return_value = mock_path_instance
        
        # Call with all Nones
        result = cmd_test_main(
            mock_ctx,
            prompt_file="prompt.prompt",
            code_file="code.py",
            output=None,
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=None,
            strength=None,
            temperature=None,
        )
        
        assert result[0] == "test"
        assert result[1] == 0.05
        assert result[2] == "gpt-4"


def test_missing_output_file_path_error(mock_ctx, basic_inputs):
    """Test error when output file path cannot be determined."""
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.resolve_effective_config") as mock_resolve_config, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("pdd.cmd_test_main.print") as mock_print:
        
        # Return None for output path
        mock_construct_paths.return_value = (
            {"strength": 0.5, "temperature": 0.0, "time": 0.25},
            {"prompt_file": "prompt", "code_file": "code"},
            {"output": None},
            "python"
        )
        
        mock_resolve_config.return_value = {
            "strength": 0.5,
            "temperature": 0.0,
            "time": 0.25,
        }
        
        mock_generate_test.return_value = ("test", 0.05, "gpt-4")
        
        result = cmd_test_main(mock_ctx, **basic_inputs)
        
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Output file path could not be determined" in result[2]