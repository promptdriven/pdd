import os
import pytest
from unittest.mock import patch, mock_open
import csv
from io import StringIO
from datetime import datetime
from click.testing import CliRunner
from pdd.cli import cli

@pytest.fixture
def runner() -> CliRunner:
    """Fixture to provide a Click CLI runner for testing."""
    return CliRunner()

def test_cli_version(runner: CliRunner) -> None:
    """Test the CLI version command."""
    result = runner.invoke(cli, ['--version'])
    assert result.exit_code == 0
    assert '0.1.0' in result.output

def test_cli_help(runner: CliRunner) -> None:
    """Test the CLI help command."""
    result = runner.invoke(cli, ['--help'])
    assert result.exit_code == 0
    assert 'PDD (Prompt-Driven Development) Command Line Interface' in result.output
    
def test_generate_command(runner: CliRunner, tmp_path) -> None:
    """Test the generate command of the CLI."""
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    output_file = tmp_path / "output.py"
    
    result = runner.invoke(cli, ['generate', str(prompt_file), '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Generated code saved to:" in result.output
    assert output_file.exists()

def test_example_command(runner: CliRunner, tmp_path) -> None:
    """Test the example command of the CLI."""
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    code_file = tmp_path / "code.py"
    code_file.write_text("def add(a, b): return a + b")
    output_file = tmp_path / "example.py"
    
    result = runner.invoke(cli, ['example', str(prompt_file), str(code_file), '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Generated example code saved to:" in result.output
    assert output_file.exists()

def test_test_command(runner: CliRunner, tmp_path) -> None:
    """Test the test command of the CLI."""
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    code_file = tmp_path / "code.py"
    code_file.write_text("def add(a, b): return a + b")
    output_file = tmp_path / "test_output.py"
    
    result = runner.invoke(cli, ['test', str(prompt_file), str(code_file), '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Generated unit test saved to:" in result.output
    assert output_file.exists()

def test_preprocess_command(runner: CliRunner, tmp_path) -> None:
    """Test the preprocess command of the CLI."""
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("<include>test.txt</include>")
    output_file = tmp_path / "preprocessed.txt"
    
    result = runner.invoke(cli, ['preprocess', str(prompt_file), '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Preprocessed prompt saved to:" in result.output
    assert output_file.exists()

def test_fix_command(runner: CliRunner, tmp_path) -> None:
    """Test the fix command of the CLI."""
    from unittest.mock import patch
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    code_file = tmp_path / "code.py"
    # Introduce an error in the code that needs fixing
    code_file.write_text("def add(a, b): return a * b")
    unit_test_file = tmp_path / "test_code.py"
    unit_test_file.write_text("def test_add(): assert add(1, 2) == 3")
    error_file = tmp_path / "error.txt"
    error_file.write_text("AssertionError: assert 2 == 3")
    output_test = tmp_path / "fixed_test.py"
    output_code = tmp_path / "fixed_code.py"
 
    # Mock the function that interacts with the LLM
    with patch('pdd.cli.fix_errors_from_unit_tests', return_value=(True, True, 'fixed test content', 'fixed code content', 0.0, 'mock_model')):
        result = runner.invoke(cli, ['--force', 'fix', str(prompt_file), str(code_file), str(unit_test_file), str(error_file),
                                     '--output-test', str(output_test), '--output-code', str(output_code)])
        assert result.exit_code == 0
        assert "Fixed unit test saved to:" in result.output
        assert "Fixed code saved to:" in result.output
        assert output_test.exists()
        assert output_code.exists()

def test_split_command(runner: CliRunner, tmp_path) -> None:
    """Test the split command of the CLI."""
    input_prompt = tmp_path / "input_prompt.txt"
    input_prompt.write_text("Generate a complex Python program")
    input_code = tmp_path / "input_code.py"
    input_code.write_text("def complex_function(): pass")
    example_code = tmp_path / "example_code.py"
    example_code.write_text("complex_function()")
    output_sub = tmp_path / "sub_prompt.txt"
    output_modified = tmp_path / "modified_prompt.txt"
    
    result = runner.invoke(cli, ['split', str(input_prompt), str(input_code), str(example_code),
                                 '--output-sub', str(output_sub), '--output-modified', str(output_modified)])
    assert result.exit_code == 0
    assert "Sub-prompt saved to:" in result.output
    assert "Modified prompt saved to:" in result.output
    assert output_sub.exists()
    assert output_modified.exists()

def test_change_command(runner: CliRunner, tmp_path) -> None:
    """Test the change command of the CLI."""
    input_prompt_file = tmp_path / "input_prompt.txt"
    input_prompt_file.write_text("Generate a Python function to add two numbers")
    input_code_file = tmp_path / "input_code.py"
    input_code_file.write_text("def add(a, b): return a + b")
    change_prompt_file = tmp_path / "change_prompt.txt"
    change_prompt_file.write_text("Modify the function to multiply instead of add")
    output_file = tmp_path / "modified_prompt.txt"
    
    result = runner.invoke(cli, ['change', str(input_prompt_file), str(input_code_file), str(change_prompt_file),
                                 '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Modified prompt saved to:" in result.output
    assert output_file.exists()

def test_update_command(runner: CliRunner, tmp_path) -> None:
    """Test the update command of the CLI."""
    input_prompt_file = tmp_path / "input_prompt.txt"
    input_prompt_file.write_text("Generate a Python function to add two numbers")
    input_code_file = tmp_path / "input_code.py"
    input_code_file.write_text("def add(a, b): return a + b")
    modified_code_file = tmp_path / "modified_code.py"
    modified_code_file.write_text("def add(a, b): return a * b")
    output_file = tmp_path / "updated_prompt.txt"
    
    result = runner.invoke(cli, ['update', str(input_prompt_file), str(input_code_file), str(modified_code_file),
                                 '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Updated prompt saved to:" in result.output
    assert output_file.exists()

def test_detect_command(runner: CliRunner, tmp_path) -> None:
    """Test the detect command of the CLI."""
    prompt_file1 = tmp_path / "prompt1.txt"
    prompt_file1.write_text("Generate a Python function to add two numbers")
    prompt_file2 = tmp_path / "prompt2.txt"
    prompt_file2.write_text("Generate a Python function to multiply two numbers")
    change_file = tmp_path / "change.txt"
    change_file.write_text("Update all arithmetic operations to use floating-point numbers")
    output_file = tmp_path / "detect_results.csv"
    
    result = runner.invoke(cli, ['detect', str(prompt_file1), str(prompt_file2), str(change_file),
                                 '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Analysis results saved to:" in result.output
    assert output_file.exists()

def test_conflicts_command(runner: CliRunner, tmp_path) -> None:
    """Test the conflicts command of the CLI."""
    from unittest.mock import patch
    prompt1 = tmp_path / "prompt1.txt"
    prompt1.write_text("Generate a Python function to add two numbers")
    prompt2 = tmp_path / "prompt2.txt"
    prompt2.write_text("Generate a Python function to subtract two numbers")
    output_file = tmp_path / "conflicts_results.csv"

    # Mock the function that interacts with the LLM
    with patch('pdd.cli.conflicts_in_prompts', return_value=([{
        'description': 'Conflict in function names',
        'explanation': 'Both functions are named differently but could cause confusion.',
        'suggestion1': 'Rename function in prompt1 to sum_numbers.',
        'suggestion2': 'Rename function in prompt2 to subtract_numbers.'
    }], 0.0, 'mock_model')):
        result = runner.invoke(cli, ['conflicts', str(prompt1), str(prompt2), '--output', str(output_file)])
        assert result.exit_code == 0
        assert "Conflict analysis results saved to:" in result.output
        assert output_file.exists()

def test_crash_command(runner: CliRunner, tmp_path) -> None:
    """Test the crash command of the CLI."""
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("Generate a Python function to divide two numbers")
    code_file = tmp_path / "code.py"
    code_file.write_text("def divide(a, b): return a / b")
    program_file = tmp_path / "program.py"
    program_file.write_text("from code import divide\nresult = divide(10, 0)")
    error_file = tmp_path / "error.txt"
    error_file.write_text("ZeroDivisionError: division by zero")
    output_file = tmp_path / "fixed_code.py"
    
    result = runner.invoke(cli, ['crash', str(prompt_file), str(code_file), str(program_file), str(error_file),
                                 '--output', str(output_file)])
    assert result.exit_code == 0
    assert "Fixed code saved to:" in result.output
    assert output_file.exists()

def test_install_completion_command(runner: CliRunner, tmp_path) -> None:
    """Test the install-completion command of the CLI."""
    with runner.isolated_filesystem() as fs:
        home_dir = os.path.join(fs, "home", "user")
        os.makedirs(home_dir)
        bashrc_file = os.path.join(home_dir, ".bashrc")
        with open(bashrc_file, 'w') as f:
            f.write("# Existing content")

        with patch.dict(os.environ, {'HOME': home_dir, 'SHELL': '/bin/bash'}):
            result = runner.invoke(cli, ['install-completion'])
        
        assert result.exit_code == 0
        assert "Shell completion installed for bash" in result.output
        
        with open(bashrc_file, 'r') as f:
            content = f.read()
            assert "# PDD CLI completion" in content
            assert "eval \"$(_PDD_COMPLETE=bash_source pdd)\"" in content

def test_output_cost_tracking(runner: CliRunner, tmp_path) -> None:
    """Test the output cost tracking feature of the CLI."""
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    output_file = tmp_path / "output.py"
    cost_file = tmp_path / "cost.csv"
    
    result = runner.invoke(cli, ['--output-cost', str(cost_file), 'generate', str(prompt_file), '--output', str(output_file)])
    assert result.exit_code == 0
    assert cost_file.exists()
    
    with open(cost_file, 'r') as f:
        content = f.read()
        assert 'timestamp,model,command,cost,input_files,output_files' in content
        assert 'generate' in content
        assert str(prompt_file) in content
        assert str(output_file) in content

def test_output_cost_tracking(runner: CliRunner, tmp_path) -> None:
    """Test the output cost tracking feature of the CLI."""
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    output_file = tmp_path / "output.py"
    cost_file = tmp_path / "cost.csv"
    
    result = runner.invoke(cli, ['--output-cost', str(cost_file), 'generate', str(prompt_file), '--output', str(output_file)])
    assert result.exit_code == 0
    assert cost_file.exists()
    
    with open(cost_file, 'r') as f:
        content = f.read()
        assert 'timestamp,model,command,cost,input_files,output_files' in content
        assert 'generate' in content
        assert str(prompt_file) in content
        assert str(output_file) in content

@pytest.fixture
def csv_output():
    return StringIO()

@patch('os.path.isfile', return_value=True)
@patch('os.path.getsize', return_value=0)
def test_track_cost_decorator(mock_getsize, mock_isfile, runner: CliRunner, csv_output, tmp_path):
    from unittest.mock import patch, mock_open
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    output_file = tmp_path / "output.py"
    cost_file = tmp_path / "cost.csv"

    # Mock the code_generator function
    with patch('pdd.cli.code_generator', return_value=('def add(a, b): return a + b', 0.0, 'mock_model')):
        # Adjust the patching of open to only affect the cost file
        with patch('builtins.open', new_callable=mock_open()) as mock_file:
            # Set the mock to affect only the cost file
            mock_file.return_value.__enter__.return_value = csv_output
            mock_getsize.return_value = 0

            result = runner.invoke(cli, ['--output-cost', str(cost_file), 'generate', str(prompt_file), '--output', str(output_file)])

            assert result.exit_code == 0

    # Reset the StringIO cursor
    csv_output.seek(0)

    # Read the CSV content
    csv_reader = csv.reader(csv_output)
    header = next(csv_reader)
    data = next(csv_reader)

    # Check the CSV header
    assert header == ['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files']

    # Check the data
    assert data[2] == 'generate'  # command
    assert float(data[3]) >= 0  # cost
    assert str(prompt_file) in data[4]  # input_files
    assert str(output_file) in data[5]  # output_files

    # Check if timestamp is in the correct format
    datetime.fromisoformat(data[0])  # This will raise an exception if the format is incorrect

    # Check if model is not empty
    assert data[1]  # model should not be empty