# tests/test_cli.py
import os
import sys
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock

import pytest
from click.testing import CliRunner

# Assuming 'pdd' package is installed or in PYTHONPATH
# Adjust import if necessary based on project structure
from pdd import cli, __version__, DEFAULT_STRENGTH

# Helper to create dummy files
@pytest.fixture
def create_dummy_files(tmp_path):
    files = {}
    def _create_files(*filenames, content="dummy content"):
        for name in filenames:
            file_path = tmp_path / name
            file_path.parent.mkdir(parents=True, exist_ok=True)
            file_path.write_text(content)
            files[name] = file_path
        return files
    return _create_files

@pytest.fixture
def runner():
    return CliRunner()

# --- Basic CLI Tests ---

def test_cli_version(runner):
    """Test `pdd --version`."""
    result = runner.invoke(cli.cli, ["--version"])
    assert result.exit_code == 0
    assert __version__ in result.output

def test_cli_help(runner):
    """Test `pdd --help`."""
    result = runner.invoke(cli.cli, ["--help"])
    assert result.exit_code == 0
    assert "Usage: cli [OPTIONS] COMMAND1" in result.output
    # Check if a few commands are listed
    assert "generate" in result.output
    assert "fix" in result.output
    assert "install_completion" in result.output

def test_cli_command_help(runner):
    """Test `pdd [COMMAND] --help`."""
    result = runner.invoke(cli.cli, ["generate", "--help"])
    assert result.exit_code == 0
    assert "Usage: cli generate [OPTIONS] PROMPT_FILE" in result.output
    assert "--output" in result.output

# --- Global Options Tests ---

@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_global_options_defaults(mock_construct, mock_main, runner, create_dummy_files):
    """Test default global options are passed in context."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')
    mock_main.return_value = ('code', 0.0, 'model')

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])

    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx is not None
    assert ctx.obj['force'] is False
    assert ctx.obj['strength'] == DEFAULT_STRENGTH
    assert ctx.obj['temperature'] == 0.0
    assert ctx.obj['verbose'] is False
    assert ctx.obj['quiet'] is False
    assert ctx.obj['output_cost'] is None
    assert ctx.obj['local'] is False

@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_global_options_explicit(mock_construct, mock_main, runner, create_dummy_files):
    """Test explicit global options override defaults."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')
    mock_main.return_value = ('code', 0.0, 'model')

    result = runner.invoke(cli.cli, [
        "--force",
        "--strength", "0.9",
        "--temperature", "0.5",
        "--verbose",
        "--output-cost", "costs.csv",
        "--local",
        "generate", str(files["test.prompt"])
    ])

    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx is not None
    assert ctx.obj['force'] is True
    assert ctx.obj['strength'] == 0.9
    assert ctx.obj['temperature'] == 0.5
    assert ctx.obj['verbose'] is True # Not overridden by quiet
    assert ctx.obj['quiet'] is False
    assert ctx.obj['output_cost'] == "costs.csv"
    assert ctx.obj['local'] is True

@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_global_options_quiet_overrides_verbose(mock_construct, mock_main, runner, create_dummy_files):
    """Test --quiet overrides --verbose."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')
    mock_main.return_value = ('code', 0.0, 'model')

    result = runner.invoke(cli.cli, [
        "--verbose",
        "--quiet",
        "generate", str(files["test.prompt"])
    ])

    assert result.exit_code == 0
    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get('ctx')
    assert ctx is not None
    assert ctx.obj['verbose'] is False # Should be forced to False
    assert ctx.obj['quiet'] is True

# --- Auto Update Tests ---

@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main') # Need to mock a command to trigger cli execution
@patch('pdd.cli.construct_paths')
def test_cli_auto_update_called_by_default(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is called by default."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')
    mock_main.return_value = ('code', 0.0, 'model')

    runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])
    mock_auto_update.assert_called_once_with(quiet=False)

@patch.dict(os.environ, {"PDD_AUTO_UPDATE": "false"}, clear=True)
@patch('pdd.cli.auto_update')
@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_auto_update_not_called_when_disabled(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update is not called when PDD_AUTO_UPDATE=false."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')
    mock_main.return_value = ('code', 0.0, 'model')

    runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])
    mock_auto_update.assert_not_called()

@patch('pdd.cli.auto_update', side_effect=Exception("Network error"))
@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.construct_paths')
def test_cli_auto_update_handles_exception(mock_construct, mock_main, mock_auto_update, runner, create_dummy_files):
    """Test auto_update exceptions are handled gracefully."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')
    mock_main.return_value = ('code', 0.0, 'model')

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])
    # Should still proceed and exit cleanly from the command itself
    assert result.exit_code == 0
    assert "Auto-update check failed" in result.output
    assert "Network error" in result.output
    mock_main.assert_called_once() # Ensure command still ran

# --- Error Handling Tests ---

@patch('pdd.cli.construct_paths', side_effect=FileNotFoundError("Input file missing"))
@patch('pdd.cli.code_generator_main') # Mock main to prevent it running
def test_cli_handle_error_filenotfound(mock_main, mock_construct, runner):
    """Test handle_error for FileNotFoundError."""
    # No need to create file as construct_paths will raise error
    result = runner.invoke(cli.cli, ["generate", "nonexistent.prompt"])
    assert result.exit_code == 1
    assert "Error during 'generate' command" in result.output
    assert "File not found" in result.output
    assert "Input file missing" in result.output
    mock_main.assert_not_called()

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.code_generator_main', side_effect=ValueError("Invalid prompt content"))
def test_cli_handle_error_valueerror(mock_main, mock_construct, runner, create_dummy_files):
    """Test handle_error for ValueError."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])
    assert result.exit_code == 1
    assert "Error during 'generate' command" in result.output
    assert "Input/Output Error" in result.output # ValueError maps to this
    assert "Invalid prompt content" in result.output

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.code_generator_main', side_effect=Exception("Unexpected LLM issue"))
def test_cli_handle_error_generic(mock_main, mock_construct, runner, create_dummy_files):
    """Test handle_error for generic Exception."""
    files = create_dummy_files("test.prompt")
    mock_construct.return_value = ({}, {'output': 'out.py'}, 'python')

    result = runner.invoke(cli.cli, ["generate", str(files["test.prompt"])])
    assert result.exit_code == 1
    assert "Error during 'generate' command" in result.output
    assert "An unexpected error occurred" in result.output
    assert "Unexpected LLM issue" in result.output

@patch('pdd.cli.construct_paths', side_effect=FileNotFoundError("Input file missing"))
@patch('pdd.cli.code_generator_main')
def test_cli_handle_error_quiet(mock_main, mock_construct, runner):
    """Test handle_error respects --quiet."""
    result = runner.invoke(cli.cli, ["--quiet", "generate", "nonexistent.prompt"])
    assert result.exit_code == 1
    # Error messages should be suppressed
    assert "Error during 'generate' command" not in result.output
    assert "File not found" not in result.output
    mock_main.assert_not_called()

# --- construct_paths Integration Tests ---

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.code_generator_main')
def test_cli_construct_paths_called_correctly(mock_main, mock_construct, runner, create_dummy_files):
    """Test construct_paths is called with correct arguments."""
    files = create_dummy_files("my_prompt.prompt")
    prompt_path_str = str(files["my_prompt.prompt"])
    output_path = "output/dir/"
    mock_construct.return_value = ({'prompt_file': 'content'}, {'output': 'output/dir/my_prompt.py'}, 'python')
    mock_main.return_value = ('code', 0.0, 'model')

    runner.invoke(cli.cli, ["--force", "generate", prompt_path_str, "--output", output_path])

    mock_construct.assert_called_once_with(
        input_file_paths={"prompt_file": prompt_path_str},
        force=True,
        quiet=False,
        command="generate",
        command_options={"output": output_path}
    )
    mock_main.assert_called_once_with(
        ctx=ANY,
        prompt_file=prompt_path_str, # Check if main needs original or resolved path
        output='output/dir/my_prompt.py' # Check main gets resolved path
    )

# --- Individual Command Tests (Example: generate, fix, change) ---

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.code_generator_main')
def test_cli_generate_command(mock_main, mock_construct, runner, create_dummy_files):
    """Test the 'generate' command flow."""
    files = create_dummy_files("gen.prompt")
    prompt_path = str(files["gen.prompt"])
    resolved_output = "output/gen_impl.py"
    mock_construct.return_value = ({'prompt_file': 'prompt data'}, {'output': resolved_output}, 'python')
    mock_main.return_value = ('generated code', 0.1, 'model-gen')

    result = runner.invoke(cli.cli, ["generate", prompt_path, "--output", "output/"])

    assert result.exit_code == 0
    mock_construct.assert_called_once_with(
        input_file_paths={'prompt_file': prompt_path},
        force=False, quiet=False, command='generate', command_options={'output': 'output/'}
    )
    mock_main.assert_called_once_with(ctx=ANY, prompt_file=prompt_path, output=resolved_output)
    # Check result callback data (implicitly tested via chaining test)

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.fix_main')
def test_cli_fix_command(mock_main, mock_construct, runner, create_dummy_files):
    """Test the 'fix' command flow."""
    files = create_dummy_files("p.prompt", "c.py", "t.py", "e.log")
    prompt_p, code_p, test_p, error_p = [str(files[f]) for f in ["p.prompt", "c.py", "t.py", "e.log"]]
    resolved_out_test = "output/t_fixed.py"
    resolved_out_code = "output/c_fixed.py"
    resolved_out_results = "output/fix.log"

    mock_construct.return_value = (
        {'prompt_file': 'p', 'code_file': 'c', 'unit_test_file': 't', 'error_file': 'e'},
        {'output_test': resolved_out_test, 'output_code': resolved_out_code, 'output_results': resolved_out_results},
        'python'
    )
    # fix_main returns: success, fixed_test, fixed_code, attempts, cost, model
    mock_main.return_value = (True, 'fixed test content', 'fixed code content', 1, 0.2, 'model-fix')

    result = runner.invoke(cli.cli, [
        "fix", prompt_p, code_p, test_p, error_p,
        "--output-test", "output/",
        "--output-code", "output/",
        "--output-results", "output/fix.log",
        "--loop", # Test loop flag passing
        "--max-attempts", "5"
    ])

    assert result.exit_code == 0
    mock_construct.assert_called_once_with(
        input_file_paths={'prompt_file': prompt_p, 'code_file': code_p, 'unit_test_file': test_p, 'error_file': error_p},
        force=False, quiet=False, command='fix',
        command_options={'output_test': 'output/', 'output_code': 'output/', 'output_results': 'output/fix.log'}
    )
    mock_main.assert_called_once_with(
        ctx=ANY, prompt_file=prompt_p, code_file=code_p, unit_test_file=test_p, error_file=error_p,
        output_test=resolved_out_test, output_code=resolved_out_code, output_results=resolved_out_results,
        loop=True, verification_program=None, max_attempts=5, budget=5.0, auto_submit=False
    )

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.change_main')
def test_cli_change_command_csv_validation(mock_main, mock_construct, runner, create_dummy_files, tmp_path):
    """Test 'change' command validation for --csv."""
    files = create_dummy_files("changes.csv", "p.prompt")
    code_dir = tmp_path / "code_dir"
    code_dir.mkdir()
    (code_dir / "some_code.py").touch()

    # Error: --csv requires directory for input_code
    result = runner.invoke(cli.cli, ["change", "--csv", str(files["changes.csv"]), str(files["p.prompt"])]) # p.prompt is a file
    assert result.exit_code != 0
    assert "INPUT_CODE must be a directory when using --csv" in result.output

    # Error: Cannot use --csv and input_prompt_file
    result = runner.invoke(cli.cli, ["change", "--csv", str(files["changes.csv"]), str(code_dir), str(files["p.prompt"])])
    assert result.exit_code != 0
    assert "Cannot use --csv and specify an INPUT_PROMPT_FILE" in result.output

    # Error: Not using --csv requires input_prompt_file
    result = runner.invoke(cli.cli, ["change", str(files["changes.csv"]), str(code_dir / "some_code.py")]) # Missing input_prompt_file
    assert result.exit_code != 0
    assert "INPUT_PROMPT_FILE is required when not using --csv" in result.output

    # Error: Not using --csv requires file for input_code
    result = runner.invoke(cli.cli, ["change", str(files["changes.csv"]), str(code_dir), str(files["p.prompt"])]) # code_dir is a dir
    assert result.exit_code != 0
    assert "INPUT_CODE must be a file when not using --csv" in result.output

    # Valid CSV call
    mock_main.return_value = ({'msg': 'Processed 1 file'}, 0.3, 'model-change')
    result = runner.invoke(cli.cli, ["change", "--csv", str(files["changes.csv"]), str(code_dir)])
    assert result.exit_code == 0
    mock_main.assert_called_once_with(
        ctx=ANY, change_prompt_file=str(files["changes.csv"]), input_code=str(code_dir),
        input_prompt_file=None, output=None, use_csv=True
    )
    # construct_paths should NOT have been called in CSV mode
    mock_construct.assert_not_called()


@patch('pdd.cli.construct_paths')
@patch('pdd.cli.auto_deps_main')
def test_cli_auto_deps_strips_quotes(mock_main, mock_construct, runner, create_dummy_files, tmp_path):
    """Test that auto-deps strips quotes from directory_path."""
    files = create_dummy_files("dep.prompt")
    dep_dir_path = tmp_path / "deps"
    dep_dir_path.mkdir()
    quoted_path = f'"{dep_dir_path}/*"' # Path with quotes

    mock_construct.return_value = ({}, {'output': 'out.prompt'}, 'python')
    mock_main.return_value = ('modified prompt', 0.1, 'model-deps')

    result = runner.invoke(cli.cli, ["auto-deps", str(files["dep.prompt"]), quoted_path])

    assert result.exit_code == 0
    mock_main.assert_called_once()
    # Check that the path passed to auto_deps_main has quotes stripped
    call_args = mock_main.call_args.kwargs
    assert call_args['directory_path'] == f'{dep_dir_path}/*' # No quotes


# --- Command Chaining Tests ---

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.context_generator_main')
def test_cli_chaining_cost_aggregation(mock_example_main, mock_gen_main, mock_construct, runner, create_dummy_files):
    """Test cost aggregation for chained commands."""
    files = create_dummy_files("chain.prompt", "chain_code.py")
    prompt_p = str(files["chain.prompt"])
    code_p = str(files["chain_code.py"])

    # Mock return values for construct_paths for both commands
    mock_construct.side_effect = [
        ({'prompt_file': 'p'}, {'output': 'chain_code.py'}, 'python'), # For generate
        ({'prompt_file': 'p', 'code_file': 'c'}, {'output': 'chain_example.py'}, 'python') # For example
    ]

    # Mock return values for main functions
    mock_gen_main.return_value = ('generated code', 0.123, 'model-A')
    mock_example_main.return_value = ('example code', 0.045, 'model-B')

    result = runner.invoke(cli.cli, ["generate", prompt_p, "example", prompt_p, code_p])

    assert result.exit_code == 0
    assert "Command Chain Execution Summary" in result.output
    assert "Step 1 (generate): Cost: $0.123000, Model: model-A" in result.output
    assert "Step 2 (example): Cost: $0.045000, Model: model-B" in result.output
    assert "Total Estimated Cost for Chain: $0.168000" in result.output # 0.123 + 0.045

@patch('pdd.cli.construct_paths')
@patch('pdd.cli.code_generator_main')
@patch('pdd.cli.preprocess_main') # Preprocess doesn't have @track_cost
def test_cli_chaining_with_no_cost_command(mock_preprocess_main, mock_gen_main, mock_construct, runner, create_dummy_files):
    """Test chaining with a command that doesn't return cost info."""
    files = create_dummy_files("chain2.prompt")
    prompt_p = str(files["chain2.prompt"])

    mock_construct.side_effect = [
        ({'prompt_file': 'p'}, {'output': 'chain2_prep.prompt'}, 'python'), # For preprocess
        ({'prompt_file': 'p'}, {'output': 'chain2_code.py'}, 'python') # For generate
    ]
    # preprocess returns dummy values now
    mock_preprocess_main.return_value = None # Simulate original behavior before dummy return
    mock_gen_main.return_value = ('generated code', 0.111, 'model-C')

    # Need to patch the preprocess command function itself to return the dummy tuple
    # OR adjust the result callback to handle None/non-tuple results
    # Let's patch the command function for simplicity here
    with patch('pdd.cli.preprocess', return_value=("Preprocessing complete.", 0.0, "local")) as mock_preprocess_cmd:
        result = runner.invoke(cli.cli, ["preprocess", prompt_p, "generate", prompt_p])

        assert result.exit_code == 0
        assert "Command Chain Execution Summary" in result.output
        # Check how the callback handles the dummy return from preprocess
        assert "Step 1 (preprocess): Cost: $0.000000, Model: local" in result.output
        assert "Step 2 (generate): Cost: $0.111000, Model: model-C" in result.output
        assert "Total Estimated Cost for Chain: $0.111000" in result.output


# --- install_completion Command Test ---

@patch('pdd.cli.install_completion')
def test_cli_install_completion_cmd(mock_install_func, runner):
    """Test the install_completion command."""
    result = runner.invoke(cli.cli, ["install_completion"])
    assert result.exit_code == 0
    mock_install_func.assert_called_once_with(quiet=False)

@patch('pdd.cli.install_completion')
def test_cli_install_completion_cmd_quiet(mock_install_func, runner):
    """Test the install_completion command with --quiet."""
    result = runner.invoke(cli.cli, ["--quiet", "install_completion"])
    assert result.exit_code == 0
    mock_install_func.assert_called_once_with(quiet=True)

