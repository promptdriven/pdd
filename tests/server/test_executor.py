import sys
import io
import pytest
import click
from unittest.mock import MagicMock, patch
from dataclasses import dataclass

# Import the module to access global defaults dynamically
import pdd.server.executor as executor_module

from pdd.server.executor import (
    StreamingWriter,
    OutputCapture,
    create_isolated_context,
    ClickCommandExecutor,
    execute_pdd_command,
    CapturedOutput,
    get_pdd_command
)

# -----------------------------------------------------------------------------
# Tests for StreamingWriter
# -----------------------------------------------------------------------------

def test_streaming_writer_writes_and_calls_back():
    """Test that StreamingWriter writes to buffer and calls the callback."""
    buffer = io.StringIO()
    callback = MagicMock()
    writer = StreamingWriter(buffer, callback, "stdout")

    # Test write
    msg = "Hello World"
    writer.write(msg)

    assert buffer.getvalue() == msg
    callback.assert_called_with("stdout", msg)

    # Test isatty
    assert writer.isatty() is False

    # Test flush (should not raise error)
    writer.flush()

def test_streaming_writer_no_callback():
    """Test StreamingWriter works without a callback."""
    buffer = io.StringIO()
    writer = StreamingWriter(buffer, None, "stderr")
    writer.write("test")
    assert buffer.getvalue() == "test"

# -----------------------------------------------------------------------------
# Tests for OutputCapture
# -----------------------------------------------------------------------------

def test_output_capture_captures_streams():
    """Test that OutputCapture captures stdout and stderr."""
    callback = MagicMock()
    
    # Ensure we start with real stdout/stderr
    original_stdout = sys.stdout
    original_stderr = sys.stderr

    with OutputCapture(callback=callback) as capture:
        print("Hello Stdout")
        print("Hello Stderr", file=sys.stderr)
        
        # Verify streams are redirected
        assert sys.stdout != original_stdout
        assert sys.stderr != original_stderr

    # Verify streams are restored
    assert sys.stdout == original_stdout
    assert sys.stderr == original_stderr

    # Verify content
    assert "Hello Stdout" in capture.stdout
    assert "Hello Stderr" in capture.stderr

    # Verify callback was called
    # Note: print() might call write() multiple times (e.g. for newline)
    assert callback.call_count >= 2

# -----------------------------------------------------------------------------
# Tests for create_isolated_context
# -----------------------------------------------------------------------------

def test_create_isolated_context_defaults_and_overrides():
    """Test context creation with defaults and overrides."""
    cmd = click.Command("test")
    
    # Test defaults
    ctx = create_isolated_context(cmd)
    # Use the actual default from the module, as it might vary based on environment (0.5 or 1.0)
    assert ctx.obj["strength"] == executor_module.DEFAULT_STRENGTH
    assert ctx.obj["verbose"] is False
    
    # Test overrides
    # Pick a value distinct from the default
    override_strength = 0.9 if executor_module.DEFAULT_STRENGTH != 0.9 else 0.8
    overrides = {"strength": override_strength, "custom": "value"}
    
    ctx = create_isolated_context(cmd, obj=overrides)
    assert ctx.obj["strength"] == override_strength
    assert ctx.obj["custom"] == "value"
    assert ctx.obj["verbose"] is False  # Default preserved

    # Test parameter source mocking
    # This ensures ctx.get_parameter_source() returns a mock with name="DEFAULT"
    source = ctx.get_parameter_source("some_param")
    assert source.name == "DEFAULT"

# -----------------------------------------------------------------------------
# Tests for ClickCommandExecutor
# -----------------------------------------------------------------------------

@pytest.fixture
def executor():
    return ClickCommandExecutor()

def test_executor_success_capture(executor):
    """Test successful command execution and output capture."""
    
    @click.command()
    def dummy_cmd():
        click.echo("Success output")
        return "Result"

    output = executor.execute(dummy_cmd)

    assert output.exit_code == 0
    assert "Success output" in output.stdout
    assert output.result == "Result"
    assert output.exception is None

def test_executor_cost_extraction_tuple(executor):
    """Test extracting cost from a tuple return value."""
    
    @click.command()
    def cost_cmd():
        # (result, cost, model)
        return ("result", 0.15, "gpt-4")

    output = executor.execute(cost_cmd)
    assert output.cost == 0.15

def test_executor_cost_extraction_dict(executor):
    """Test extracting cost from a dict return value."""
    
    @click.command()
    def cost_cmd():
        return {"result": "ok", "cost": 0.25}

    output = executor.execute(cost_cmd)
    assert output.cost == 0.25

def test_executor_cost_extraction_object(executor):
    """Test extracting cost from an object with a .cost attribute."""
    
    @dataclass
    class ResultObj:
        cost: float
    
    @click.command()
    def cost_cmd():
        return ResultObj(cost=0.35)

    output = executor.execute(cost_cmd)
    assert output.cost == 0.35

def test_executor_handles_abort(executor):
    """Test handling of click.Abort."""
    
    @click.command()
    def abort_cmd():
        raise click.Abort()

    output = executor.execute(abort_cmd)
    assert output.exit_code == 1
    assert isinstance(output.exception, click.Abort)

def test_executor_handles_click_exception(executor):
    """Test handling of click.ClickException."""
    
    @click.command()
    def fail_cmd():
        raise click.ClickException("Something failed")

    output = executor.execute(fail_cmd)
    assert output.exit_code != 0
    assert "Error: Something failed" in output.stderr
    assert isinstance(output.exception, click.ClickException)

def test_executor_handles_generic_exception(executor):
    """Test handling of generic exceptions."""
    
    @click.command()
    def error_cmd():
        raise ValueError("Unexpected error")

    output = executor.execute(error_cmd)
    assert output.exit_code == 1
    assert "Exception: Unexpected error" in output.stderr
    assert isinstance(output.exception, ValueError)

def test_executor_passes_params(executor):
    """Test that parameters are passed to the command."""
    
    @click.command()
    @click.argument("name")
    def hello_cmd(name):
        click.echo(f"Hello {name}")

    output = executor.execute(hello_cmd, params={"name": "World"})
    assert "Hello World" in output.stdout

# -----------------------------------------------------------------------------
# Tests for execute_pdd_command
# -----------------------------------------------------------------------------

def test_execute_pdd_command_unknown():
    """Test executing a non-existent command."""
    output = execute_pdd_command("non_existent_command_123")
    assert output.exit_code == 1
    assert "Command 'non_existent_command_123' not found" in output.stderr
    assert isinstance(output.exception, ValueError)

def test_execute_pdd_command_success():
    """Test executing a valid command via the high-level API."""
    
    # Mock get_pdd_command to return a dummy command
    # This avoids dependency on actual PDD commands which might not be importable in test env
    mock_cmd = MagicMock(spec=click.Command)
    mock_cmd.name = "mock_cmd"
    
    # We need to mock the behavior of invoking the command
    # Since ClickCommandExecutor calls ctx.invoke(command, ...), we can't easily mock the return 
    # of invoke directly without mocking Context.
    # Instead, let's use a real click command but patch get_pdd_command to return it.
    
    @click.command()
    def real_dummy_cmd():
        click.echo("High level exec")
        return "Done"

    with patch("pdd.server.executor.get_pdd_command", return_value=real_dummy_cmd):
        output = execute_pdd_command("dummy", args={})
        
        assert output.exit_code == 0
        assert "High level exec" in output.stdout
        assert output.result == "Done"

def test_get_pdd_command_fallback():
    """Test that get_pdd_command returns None if import fails or command not found."""
    # We can't easily force an ImportError inside the function without complex mocking of sys.modules,
    # but we can test the fallback for an unknown name.
    cmd = get_pdd_command("definitely_not_a_real_command")
    assert cmd is None


def test_executor_default_strength_matches_canonical():
    """Issue #505: executor.DEFAULT_STRENGTH must match pdd.DEFAULT_STRENGTH.

    The ImportError fallback at pdd/server/executor.py:16 hardcodes
    DEFAULT_STRENGTH = 0.5, but the canonical constant in pdd/__init__.py
    is 1.0.  This test inspects the source code to verify the fallback
    value matches, catching drift even when the import succeeds at runtime.
    """
    import ast
    import pdd
    import inspect

    # Runtime check: the loaded value must match canonical
    assert executor_module.DEFAULT_STRENGTH == pdd.DEFAULT_STRENGTH, (
        f"executor.DEFAULT_STRENGTH={executor_module.DEFAULT_STRENGTH} != "
        f"pdd.DEFAULT_STRENGTH={pdd.DEFAULT_STRENGTH}"
    )

    # Source-level check: the hardcoded fallback in the except ImportError
    # block must also match the canonical value.  This catches the case where
    # the import succeeds at test time but the fallback would be wrong in a
    # different deployment environment.
    source = inspect.getsource(executor_module)
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, ast.ExceptHandler):
            for stmt in ast.walk(node):
                if (isinstance(stmt, ast.Assign)
                        and any(
                            isinstance(t, ast.Name) and t.id == "DEFAULT_STRENGTH"
                            for t in stmt.targets
                        )):
                    # Extract the hardcoded fallback value
                    value_node = stmt.value
                    if isinstance(value_node, ast.Constant):
                        assert value_node.value == pdd.DEFAULT_STRENGTH, (
                            f"Hardcoded fallback DEFAULT_STRENGTH={value_node.value} "
                            f"in executor.py ImportError handler does not match "
                            f"pdd.DEFAULT_STRENGTH={pdd.DEFAULT_STRENGTH}"
                        )