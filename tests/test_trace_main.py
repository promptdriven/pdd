import pytest
from unittest.mock import Mock, patch
from typing import Tuple, Optional
from click import Context
from pdd.trace_main import trace_main
from pdd import DEFAULT_STRENGTH


@pytest.fixture
def mock_ctx():
    """Fixture to create a mock Click context with default parameters."""
    mock_context = Mock(spec=Context)
    mock_context.obj = {
        'force': False,
        'quiet': False,
        'strength': 0.5,
        'temperature': 0.0
    }
    # Configure ctx.exit to raise SystemExit with the exit code
    def exit_side_effect(code=0):
        raise SystemExit(code)
    mock_context.exit.side_effect = exit_side_effect
    return mock_context


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_success(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main with valid inputs ensuring successful execution.
    """
    # Arrange
    prompt_file = 'prompts/test_prompt.prompt'
    code_file = 'code/test_code.py'
    code_line = 10
    output = 'output/trace_result.txt'

    # Mock construct_paths return value
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Prompt content here.",
            "code_file": "Code content here."
        },
        {
            "output": output
        },
        "python"
    )

    # Mock trace return value
    expected_return = ("15", 0.123456, "gpt-3.5-turbo")
    mock_trace.return_value = expected_return

    # Act
    result = trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert result == expected_return
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            "prompt_file": prompt_file,
            "code_file": code_file
        },
        force=False,
        quiet=False,
        command="trace",
        command_options={"output": output},
        context_override=None
    )
    mock_trace.assert_called_once_with(
        "Code content here.",
        code_line,
        "Prompt content here.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_any_call("[bold green]Trace Analysis Complete[/bold green]")
    mock_rprint.assert_any_call(f"Corresponding prompt line: [cyan]{expected_return[0]}[/cyan]")
    mock_rprint.assert_any_call(f"Total cost: [yellow]${expected_return[1]:.6f}[/yellow]")
    mock_rprint.assert_any_call(f"Model used: [magenta]{expected_return[2]}[/magenta]")


@patch('pdd.trace_main.construct_paths', side_effect=FileNotFoundError("File not found"))
@patch('pdd.trace_main.rprint')
def test_trace_main_file_not_found(mock_rprint, mock_construct_paths, mock_ctx):
    """
    Test trace_main handling when input files are not found.
    """
    # Arrange
    prompt_file = 'prompts/nonexistent_prompt.prompt'
    code_file = 'code/nonexistent_code.py'
    code_line = 5
    output = None

    # Act
    with pytest.raises(SystemExit) as exc_info:
        trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert exc_info.value.code == 1
    mock_rprint.assert_called_once_with("[bold red]File not found: File not found[/bold red]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace', side_effect=ValueError("Invalid code line"))
@patch('pdd.trace_main.rprint')
def test_trace_main_value_error(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main handling when trace analysis raises a ValueError.
    """
    # Arrange
    prompt_file = 'prompts/test_prompt.prompt'
    code_file = 'code/test_code.py'
    code_line = -1  # Invalid line number
    output = 'output/trace_result.txt'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Valid prompt content.",
            "code_file": "Valid code content."
        },
        {
            "output": output
        },
        "python"
    )

    # Act
    with pytest.raises(SystemExit) as exc_info:
        trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert exc_info.value.code == 1
    mock_trace.assert_called_once_with(
        "Valid code content.",
        code_line,
        "Valid prompt content.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_called_once_with("[bold red]Invalid input: Invalid code line[/bold red]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace', side_effect=Exception("Unexpected error"))
@patch('pdd.trace_main.rprint')
def test_trace_main_unexpected_exception(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main handling when an unexpected exception occurs.
    """
    # Arrange
    prompt_file = 'prompts/test_prompt.prompt'
    code_file = 'code/test_code.py'
    code_line = 20
    output = 'output/trace_result.txt'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Another prompt content.",
            "code_file": "Another code content."
        },
        {
            "output": output
        },
        "python"
    )

    # Act
    with pytest.raises(SystemExit) as exc_info:
        trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert exc_info.value.code == 1
    mock_trace.assert_called_once_with(
        "Another code content.",
        code_line,
        "Another prompt content.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_called_once_with("[bold red]An unexpected error occurred: Unexpected error[/bold red]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_no_output(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main when no output file is specified.
    """
    # Arrange
    prompt_file = 'prompts/test_prompt.prompt'
    code_file = 'code/test_code.py'
    code_line = 15
    output = None

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Prompt content without output.",
            "code_file": "Code content without output."
        },
        {},
        "python"
    )

    mock_trace.return_value = ("25", 0.654321, "gpt-4")

    # Act
    result = trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert result == ("25", 0.654321, "gpt-4")
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            "prompt_file": prompt_file,
            "code_file": code_file
        },
        force=False,
        quiet=False,
        command="trace",
        command_options={"output": output},
        context_override=None
    )
    mock_trace.assert_called_once_with(
        "Code content without output.",
        code_line,
        "Prompt content without output.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_any_call("[bold green]Trace Analysis Complete[/bold green]")
    mock_rprint.assert_any_call(f"Corresponding prompt line: [cyan]{'25'}[/cyan]")
    mock_rprint.assert_any_call(f"Total cost: [yellow]${0.654321:.6f}[/yellow]")
    mock_rprint.assert_any_call(f"Model used: [magenta]{'gpt-4'}[/magenta]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_quiet_mode(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main with quiet mode enabled, ensuring no output messages are printed.
    """
    # Arrange
    prompt_file = 'prompts/test_prompt.prompt'
    code_file = 'code/test_code.py'
    code_line = 8
    output = 'output/trace_result_quiet.txt'

    # Update context to set 'quiet' to True
    mock_ctx.obj['quiet'] = True

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Quiet prompt content.",
            "code_file": "Quiet code content."
        },
        {
            "output": output
        },
        "python"
    )

    mock_trace.return_value = ("30", 0.789012, "gpt-4.5")

    # Act
    result = trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert result == ("30", 0.789012, "gpt-4.5")
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            "prompt_file": prompt_file,
            "code_file": code_file
        },
        force=False,
        quiet=True,
        command="trace",
        command_options={"output": output},
        context_override=None
    )
    mock_trace.assert_called_once_with(
        "Quiet code content.",
        code_line,
        "Quiet prompt content.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_not_called()


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_force_overwrite(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main with force option enabled to overwrite existing files.
    """
    # Arrange
    prompt_file = 'prompts/force_prompt.prompt'
    code_file = 'code/force_code.py'
    code_line = 12
    output = 'output/trace_result_force.txt'

    # Update context to set 'force' to True
    mock_ctx.obj['force'] = True

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Force prompt content.",
            "code_file": "Force code content."
        },
        {
            "output": output
        },
        "python"
    )

    mock_trace.return_value = ("40", 1.234567, "gpt-5")

    # Act
    result = trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert result == ("40", 1.234567, "gpt-5")
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            "prompt_file": prompt_file,
            "code_file": code_file
        },
        force=True,
        quiet=False,
        command="trace",
        command_options={"output": output},
        context_override=None
    )
    mock_trace.assert_called_once_with(
        "Force code content.",
        code_line,
        "Force prompt content.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_any_call("[bold green]Trace Analysis Complete[/bold green]")
    mock_rprint.assert_any_call(f"Corresponding prompt line: [cyan]{'40'}[/cyan]")
    mock_rprint.assert_any_call(f"Total cost: [yellow]${1.234567:.6f}[/yellow]")
    mock_rprint.assert_any_call(f"Model used: [magenta]{'gpt-5'}[/magenta]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_zero_cost(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main ensuring that zero cost is handled correctly.
    """
    # Arrange
    prompt_file = 'prompts/zero_cost_prompt.prompt'
    code_file = 'code/zero_cost_code.py'
    code_line = 22
    output = 'output/trace_result_zero_cost.txt'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Zero cost prompt content.",
            "code_file": "Zero cost code content."
        },
        {
            "output": output
        },
        "python"
    )

    mock_trace.return_value = ("35", 0.0, "gpt-zero")

    # Act
    result = trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert result == ("35", 0.0, "gpt-zero")
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            "prompt_file": prompt_file,
            "code_file": code_file
        },
        force=False,
        quiet=False,
        command="trace",
        command_options={"output": output},
        context_override=None
    )
    mock_trace.assert_called_once_with(
        "Zero cost code content.",
        code_line,
        "Zero cost prompt content.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_any_call("[bold green]Trace Analysis Complete[/bold green]")
    mock_rprint.assert_any_call(f"Corresponding prompt line: [cyan]{'35'}[/cyan]")
    mock_rprint.assert_any_call(f"Total cost: [yellow]${0.0:.6f}[/yellow]")
    mock_rprint.assert_any_call(f"Model used: [magenta]{'gpt-zero'}[/magenta]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_missing_strength_temperature(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main when 'strength' and 'temperature' parameters are missing from context.
    """
    # Arrange
    prompt_file = 'prompts/missing_params_prompt.prompt'
    code_file = 'code/missing_params_code.py'
    code_line = 18
    output = 'output/trace_result_missing_params.txt'

    # Remove 'strength' and 'temperature' from params
    mock_ctx.obj.pop('strength', None)
    mock_ctx.obj.pop('temperature', None)

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Missing params prompt content.",
            "code_file": "Missing params code content."
        },
        {
            "output": output
        },
        "python"
    )

    mock_trace.return_value = ("50", 2.345678, "gpt-custom")

    # Act
    result = trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert result == ("50", 2.345678, "gpt-custom")
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            "prompt_file": prompt_file,
            "code_file": code_file
        },
        force=False,
        quiet=False,
        command="trace",
        command_options={"output": output},
        context_override=None
    )
    mock_trace.assert_called_once_with(
        "Missing params code content.",
        code_line,
        "Missing params prompt content.",
        DEFAULT_STRENGTH,
        0.0,   # Default temperature
        time=0.25
    )
    mock_rprint.assert_any_call("[bold green]Trace Analysis Complete[/bold green]")
    mock_rprint.assert_any_call(f"Corresponding prompt line: [cyan]{'50'}[/cyan]")
    mock_rprint.assert_any_call(f"Total cost: [yellow]${2.345678:.6f}[/yellow]")
    mock_rprint.assert_any_call(f"Model used: [magenta]{'gpt-custom'}[/magenta]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_output_file_write_failure(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main handling when writing to the output file fails.
    """
    # Arrange
    prompt_file = 'prompts/test_prompt.prompt'
    code_file = 'code/test_code.py'
    code_line = 25
    output = 'output/trace_result_write_fail.txt'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Prompt content for write failure.",
            "code_file": "Code content for write failure."
        },
        {
            "output": output
        },
        "python"
    )

    mock_trace.return_value = ("60", 3.456789, "gpt-failure")

    # Simulate file write failure
    with patch("builtins.open", side_effect=IOError("Cannot write to file")):
        with pytest.raises(SystemExit) as exc_info:
            trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert exc_info.value.code == 1
    mock_trace.assert_called_once_with(
        "Code content for write failure.",
        code_line,
        "Prompt content for write failure.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_called_with("[bold red]Error saving trace results: Cannot write to file[/bold red]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_empty_files(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main handling when input files are empty.
    """
    # Arrange
    prompt_file = 'prompts/empty_prompt.prompt'
    code_file = 'code/empty_code.py'
    code_line = 1
    output = 'output/trace_result_empty.txt'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "",
            "code_file": ""
        },
        {
            "output": output
        },
        "python"
    )

    mock_trace.return_value = ("0", 0.000000, "gpt-empty")

    # Act
    result = trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert result == ("0", 0.000000, "gpt-empty")
    mock_trace.assert_called_once_with(
        "",
        code_line,
        "",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_any_call("[bold green]Trace Analysis Complete[/bold green]")
    mock_rprint.assert_any_call(f"Corresponding prompt line: [cyan]{'0'}[/cyan]")
    mock_rprint.assert_any_call(f"Total cost: [yellow]${0.0:.6f}[/yellow]")
    mock_rprint.assert_any_call(f"Model used: [magenta]{'gpt-empty'}[/magenta]")


@patch('pdd.trace_main.construct_paths')
@patch('pdd.trace_main.trace')
@patch('pdd.trace_main.rprint')
def test_trace_main_large_code_line_number(mock_rprint, mock_trace, mock_construct_paths, mock_ctx):
    """
    Test trace_main with a code_line number that exceeds the number of lines in the code file.
    """
    # Arrange
    prompt_file = 'prompts/large_code_line.prompt'
    code_file = 'code/large_code_line.py'
    code_line = 1000  # Assuming the code file has fewer lines
    output = 'output/trace_result_large_code_line.txt'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            "prompt_file": "Prompt content for large code line.",
            "code_file": "Code content with fewer lines."
        },
        {
            "output": output
        },
        "python"
    )

    # Assume trace function handles this by raising a ValueError
    mock_trace.side_effect = ValueError("Code line number out of range")

    # Act
    with pytest.raises(SystemExit) as exc_info:
        trace_main(mock_ctx, prompt_file, code_file, code_line, output)

    # Assert
    assert exc_info.value.code == 1
    mock_trace.assert_called_once_with(
        "Code content with fewer lines.",
        code_line,
        "Prompt content for large code line.",
        0.5,
        0.0,
        time=0.25
    )
    mock_rprint.assert_called_once_with("[bold red]Invalid input: Code line number out of range[/bold red]")
