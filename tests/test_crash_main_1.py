"""
Test suite for crash_main.py

DETAILED TEST PLAN:
===================

The crash_main function is a CLI wrapper for fixing crashed code modules and their calling programs.
It orchestrates multiple components including config resolution, path construction, and either
fix_code_loop (loop mode) or fix_code_module_errors (non-loop mode).

EDGE CASES AND TEST STRATEGY:
------------------------------

1. CONTEXT OBJECT HANDLING:
   - Test with None ctx.obj (should convert to empty dict)
   - Test with None ctx.params (should convert to empty dict)
   - Test with valid dictionaries
   Strategy: Unit tests - need to verify defensive initialization

2. LOOP MODE VS NON-LOOP MODE:
   - Loop mode: calls fix_code_loop, returns specific tuple order
   - Non-loop mode: calls fix_code_module_errors with different tuple order
   Strategy: Unit tests with mocking - verify correct function is called and return values are mapped correctly

3. FILE I/O AND PATH HANDLING:
   - Valid input files
   - Missing input files (FileNotFoundError)
   - Output path creation (parent directories)
   - With and without output/output_program paths
   Strategy: Unit tests with temp directories and mocked construct_paths

4. CONFIGURATION RESOLUTION:
   - Parameter overrides for strength/temperature
   - Default values
   - Config from pddrc
   Strategy: Unit tests with mocked resolve_effective_config

5. ERROR HANDLING:
   - FileNotFoundError should return error tuple
   - click.Abort should be re-raised
   - Generic exceptions should return error tuple
   Strategy: Unit tests with exception injection

6. CONTENT TRACKING:
   - Code updated vs not updated
   - Program updated vs not updated
   - Empty final_code/final_program fallback to original
   Strategy: Unit tests comparing final vs original content

7. OUTPUT AND LOGGING:
   - quiet flag suppresses output
   - verbose flag adds diagnostics
   - Success/failure messages
   Strategy: Unit tests capturing rprint calls

8. RETURN VALUE VALIDATION:
   - Success flag correctness
   - Final code/program strings
   - Attempts count
   - Cost tracking
   - Model name
   Strategy: Unit tests validating return tuple

Z3 FORMAL VERIFICATION CONSIDERATIONS:
--------------------------------------
Z3 formal verification is NOT well-suited for this function because:
- Heavy file I/O operations
- External API calls (LLM)
- Complex orchestration logic
- Side effects (file writing, console output)
- Stateful click.Context object

Z3 is better for:
- Pure mathematical functions
- Invariant checking
- Constraint solving

Therefore, this test suite uses UNIT TESTS exclusively with mocking for dependencies.

TEST IMPLEMENTATION:
-------------------
Each test function focuses on a specific scenario with clear assertions.
Mocking is used for external dependencies (construct_paths, fix_code_loop, etc.)
to isolate the function under test and verify orchestration logic.
"""

import pytest
from unittest.mock import Mock, MagicMock, patch, mock_open
import click

# Import the actual function from the actual module
from pdd.crash_main import crash_main


class TestCrashMainContextHandling:
    """Test defensive handling of ctx.obj and ctx.params"""

    def test_none_ctx_obj_converted_to_dict(self) -> None:
        """Test that None ctx.obj is converted to empty dict"""
        ctx = Mock(spec=click.Context)
        ctx.obj = None
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "prompt", "code_file": "code", "program_file": "prog", "error_file": "err"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "prog", "code", "fix", 0.0, "model")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt"
            )

            # Verify ctx.obj is now a dict (not None)
            assert isinstance(ctx.obj, dict)

    def test_none_ctx_params_converted_to_dict(self) -> None:
        """Test that None ctx.params is converted to empty dict"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = None

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "prompt", "code_file": "code", "program_file": "prog", "error_file": "err"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "prog", "code", "fix", 0.0, "model")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt"
            )

            # Verify ctx.params is now a dict (not None)
            assert isinstance(ctx.params, dict)


class TestCrashMainLoopMode:
    """Test loop mode functionality"""

    def test_loop_mode_calls_fix_code_loop(self) -> None:
        """Test that loop=True calls fix_code_loop with correct arguments"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_loop') as mock_loop:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.6, "temperature": 0.2, "time": True},
                {"prompt_file": "prompt_content", "code_file": "code_content",
                 "program_file": "prog_content", "error_file": "err_content"},
                {"output": "out.py", "output_program": "prog_out.py"},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.6, "temperature": 0.2, "time": True}
            mock_loop.return_value = (True, "fixed_prog", "fixed_code", 3, 1.5, "gpt-4")

            with patch('builtins.open', mock_open()):
                success, code, prog, attempts, cost, model = crash_main(
                    ctx, "prompt.txt", "code.py", "prog.py", "err.txt",
                    output="out.py", output_program="prog_out.py",
                    loop=True, max_attempts=5, budget=10.0, agentic_fallback=True
                )

            # Verify fix_code_loop was called with correct args
            mock_loop.assert_called_once()
            args = mock_loop.call_args[0]
            assert args[0] == "code.py"  # code_file
            assert args[1] == "prompt_content"  # prompt_content
            assert args[2] == "prog.py"  # program_file
            assert args[3] == 0.6  # strength
            assert args[4] == 0.2  # temperature
            assert args[5] == 5  # max_attempts
            assert args[6] == 10.0  # budget

            # Verify return values mapped correctly
            assert success is True
            assert code == "fixed_code"
            assert prog == "fixed_prog"
            assert attempts == 3
            assert cost == 1.5
            assert model == "gpt-4"

    def test_loop_mode_empty_final_code_falls_back_to_original(self) -> None:
        """Test that empty final_code from fix_code_loop falls back to original"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_loop') as mock_loop:

            # Setup mocks - fix_code_loop returns empty strings
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "prompt", "code_file": "original_code",
                 "program_file": "original_prog", "error_file": "err"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_loop.return_value = (False, "", "", 3, 1.0, "model")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt", loop=True
            )

            # Verify fallback to original
            assert code == "original_code"
            assert prog == "original_prog"


class TestCrashMainNonLoopMode:
    """Test non-loop mode functionality"""

    def test_non_loop_mode_calls_fix_code_module_errors(self) -> None:
        """Test that loop=False calls fix_code_module_errors"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.7, "temperature": 0.1, "time": False},
                {"prompt_file": "prompt", "code_file": "code",
                 "program_file": "prog", "error_file": "error"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.7, "temperature": 0.1, "time": False}
            mock_fix.return_value = (True, True, "fixed_prog", "fixed_code", "raw", 0.5, "gpt-3.5")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt", loop=False
            )

            # Verify fix_code_module_errors was called
            mock_fix.assert_called_once_with(
                "prog", "prompt", "code", "error",
                0.7, 0.1, False, False
            )

            # Verify return values
            assert success is True
            assert code == "fixed_code"
            assert prog == "fixed_prog"
            assert attempts == 1
            assert cost == 0.5
            assert model == "gpt-3.5"

    def test_non_loop_mode_respects_update_flags(self) -> None:
        """Test that update_code and update_program flags are respected"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks - update_program=False, update_code=True
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "prompt", "code_file": "original_code",
                 "program_file": "original_prog", "error_file": "error"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, True, "fixed_prog", "fixed_code", "raw", 0.5, "model")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt"
            )

            # Program should remain original, code should be updated
            assert code == "fixed_code"
            assert prog == "original_prog"

    def test_non_loop_mode_empty_fixed_code_with_update_true_falls_back(self) -> None:
        """Test that empty fixed_code but update_code=True falls back to original"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks - update flags true but empty fixed content
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "prompt", "code_file": "original_code",
                 "program_file": "original_prog", "error_file": "error"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (True, True, "   ", "  ", "raw", 0.5, "model")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt"
            )

            # Should fallback to original
            assert code == "original_code"
            assert prog == "original_prog"


class TestCrashMainFileIO:
    """Test file I/O and path handling"""

    def test_output_files_written_with_parent_directories_created(self) -> None:
        """Test that output files are written and parent dirs are created"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix, \
             patch('pdd.crash_main.Path') as mock_path_class:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "prompt", "code_file": "code",
                 "program_file": "prog", "error_file": "error"},
                {"output": "/deep/path/output.py", "output_program": "/deep/path/prog.py"},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (True, True, "fixed_prog", "fixed_code", "raw", 0.5, "model")

            # Mock Path objects
            mock_code_path = MagicMock()
            mock_prog_path = MagicMock()
            mock_path_class.side_effect = [mock_code_path, mock_prog_path]

            with patch('builtins.open', mock_open()) as mock_file:
                success, code, prog, attempts, cost, model = crash_main(
                    ctx, "prompt.txt", "code.py", "prog.py", "err.txt",
                    output="/deep/path/output.py",
                    output_program="/deep/path/prog.py"
                )

            # Verify parent directories created
            mock_code_path.parent.mkdir.assert_called_once_with(parents=True, exist_ok=True)
            mock_prog_path.parent.mkdir.assert_called_once_with(parents=True, exist_ok=True)

            # Verify files written
            assert mock_file.call_count == 2

    def test_no_output_files_written_when_paths_not_specified(self) -> None:
        """Test that files are not written when output paths are None"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix, \
             patch('builtins.open', mock_open()) as mock_file:

            # Setup mocks with no output paths
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "prompt", "code_file": "code",
                 "program_file": "prog", "error_file": "error"},
                {},  # No output paths
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (True, True, "fixed_prog", "fixed_code", "raw", 0.5, "model")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt"
            )

            # Verify no files written
            mock_file.assert_not_called()


class TestCrashMainErrorHandling:
    """Test error handling scenarios"""

    def test_file_not_found_returns_error_tuple(self) -> None:
        """Test FileNotFoundError returns error tuple instead of sys.exit"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct:
            # Simulate FileNotFoundError
            mock_construct.side_effect = FileNotFoundError("input.txt not found")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt"
            )

            # Verify error tuple returned
            assert success is False
            assert code == ""
            assert prog == ""
            assert attempts == 0
            assert cost == 0.0
            assert "FileNotFoundError" in model

    def test_click_abort_is_reraised(self) -> None:
        """Test that click.Abort is re-raised for orchestrator"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct:
            # Simulate click.Abort
            mock_construct.side_effect = click.Abort()

            # Verify exception is re-raised
            with pytest.raises(click.Abort):
                crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

    def test_generic_exception_returns_error_tuple(self) -> None:
        """Test generic exceptions return error tuple"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct:
            # Simulate generic exception
            mock_construct.side_effect = ValueError("Something went wrong")

            success, code, prog, attempts, cost, model = crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt"
            )

            # Verify error tuple returned
            assert success is False
            assert code == ""
            assert prog == ""
            assert attempts == 0
            assert cost == 0.0
            assert "Error:" in model
            assert "Something went wrong" in model


class TestCrashMainConfigResolution:
    """Test configuration resolution"""

    def test_strength_temperature_overrides_passed_to_resolve_effective_config(self) -> None:
        """Test that strength/temperature params are passed as overrides"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.9, "temperature": 0.8, "time": True}
            mock_fix.return_value = (False, False, "p", "c", "r", 0.0, "m")

            crash_main(
                ctx, "prompt.txt", "code.py", "prog.py", "err.txt",
                strength=0.9, temperature=0.8
            )

            # Verify resolve_effective_config called with param_overrides
            mock_resolve.assert_called_once()
            call_kwargs = mock_resolve.call_args[1]
            assert call_kwargs["param_overrides"]["strength"] == 0.9
            assert call_kwargs["param_overrides"]["temperature"] == 0.8

    def test_none_strength_temperature_not_passed_as_overrides(self) -> None:
        """Test that None strength/temperature are still passed in param_overrides"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "p", "c", "r", 0.0, "m")

            crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

            # Verify resolve_effective_config called
            mock_resolve.assert_called_once()
            call_kwargs = mock_resolve.call_args[1]
            assert "param_overrides" in call_kwargs


class TestCrashMainOutputAndLogging:
    """Test output and logging behavior"""

    def test_quiet_suppresses_output(self) -> None:
        """Test that quiet=True suppresses rprint output"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix, \
             patch('pdd.crash_main.rprint') as mock_rprint:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "p", "c", "r", 0.5, "model")

            crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

            # Verify no rprint calls made
            mock_rprint.assert_not_called()

    def test_not_quiet_prints_status_and_cost(self) -> None:
        """Test that quiet=False prints status and cost information"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": False, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix, \
             patch('pdd.crash_main.rprint') as mock_rprint:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "p", "c", "r", 1.25, "gpt-4")

            crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

            # Verify rprint was called
            assert mock_rprint.call_count > 0

            # Check for key information in rprint calls
            all_calls = [str(call) for call in mock_rprint.call_args_list]
            all_output = " ".join(all_calls)
            assert "gpt-4" in all_output or any("model" in str(c).lower() for c in mock_rprint.call_args_list)

    def test_verbose_adds_diagnostics(self) -> None:
        """Test that verbose=True adds diagnostic output"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": False, "verbose": True, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix, \
             patch('pdd.crash_main.rprint') as mock_rprint:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "p", "c", "r", 0.5, "model")

            crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

            # Verify verbose diagnostics printed
            all_calls = [str(call) for call in mock_rprint.call_args_list]
            all_output = " ".join(all_calls)
            assert any("verbose" in str(c).lower() or "diagnostic" in str(c).lower()
                       for c in mock_rprint.call_args_list)


class TestCrashMainContentTracking:
    """Test content modification tracking"""

    def test_code_updated_flag_when_content_changes(self) -> None:
        """Test that code_updated flag is set when content changes"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": False, "verbose": True, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix, \
             patch('pdd.crash_main.rprint') as mock_rprint:

            # Setup mocks - code changes
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "original_code",
                 "program_file": "original_prog", "error_file": "e"},
                {"output": "out.py", "output_program": "prog.py"},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, True, "original_prog", "CHANGED_CODE", "r", 0.5, "m")

            with patch('builtins.open', mock_open()):
                crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt",
                           output="out.py", output_program="prog.py")

            # Check verbose output mentions code was updated
            all_calls = [str(call) for call in mock_rprint.call_args_list]
            # Should indicate code was updated
            assert any("Code updated: True" in str(c) for c in mock_rprint.call_args_list)

    def test_code_not_updated_when_content_same(self) -> None:
        """Test that code_updated is False when content doesn't change"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": False, "verbose": True, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix, \
             patch('pdd.crash_main.rprint') as mock_rprint:

            # Setup mocks - code doesn't change
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "same_code",
                 "program_file": "same_prog", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "same_prog", "same_code", "r", 0.5, "m")

            crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

            # Check verbose output mentions code was not updated
            assert any("Code updated: False" in str(c) for c in mock_rprint.call_args_list)


class TestCrashMainConstructPathsIntegration:
    """Test integration with construct_paths"""

    def test_context_override_and_confirm_callback_passed(self) -> None:
        """Test that context_override and confirm_callback are passed to construct_paths"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {
            'context': 'custom_context',
            'confirm_callback': lambda x: True
        }
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (False, False, "p", "c", "r", 0.0, "m")

            crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

            # Verify construct_paths called with context_override and confirm_callback
            mock_construct.assert_called_once()
            call_kwargs = mock_construct.call_args[1]
            assert call_kwargs["context_override"] == 'custom_context'
            assert call_kwargs["confirm_callback"] is not None


class TestCrashMainReturnValues:
    """Test return value validation"""

    def test_return_tuple_structure(self) -> None:
        """Test that return tuple has correct structure"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_module_errors') as mock_fix:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_fix.return_value = (True, True, "prog", "code", "r", 2.5, "gpt-4")

            result = crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt")

            # Verify tuple structure
            assert len(result) == 6
            success, code, prog, attempts, cost, model = result
            assert isinstance(success, bool)
            assert isinstance(code, str)
            assert isinstance(prog, str)
            assert isinstance(attempts, int)
            assert isinstance(cost, float)
            assert isinstance(model, str)

    def test_loop_mode_default_max_attempts_and_budget(self) -> None:
        """Test that loop mode uses default max_attempts=3 and budget=5.0"""
        ctx = Mock(spec=click.Context)
        ctx.obj = {}
        ctx.params = {"quiet": True, "verbose": False, "force": False}

        with patch('pdd.crash_main.construct_paths') as mock_construct, \
             patch('pdd.crash_main.resolve_effective_config') as mock_resolve, \
             patch('pdd.crash_main.fix_code_loop') as mock_loop:

            # Setup mocks
            mock_construct.return_value = (
                {"strength": 0.5, "temperature": 0.0, "time": False},
                {"prompt_file": "p", "code_file": "c", "program_file": "pr", "error_file": "e"},
                {},
                "python"
            )
            mock_resolve.return_value = {"strength": 0.5, "temperature": 0.0, "time": False}
            mock_loop.return_value = (True, "prog", "code", 2, 1.0, "model")

            with patch('builtins.open', mock_open()):
                crash_main(ctx, "prompt.txt", "code.py", "prog.py", "err.txt", loop=True)

            # Verify defaults used
            call_args = mock_loop.call_args[0]
            assert call_args[5] == 3  # max_attempts default
            assert call_args[6] == 5.0  # budget default


if __name__ == "__main__":
    pytest.main([__file__, "-v"])