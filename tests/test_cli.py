import os
import pytest
from unittest.mock import patch, mock_open, MagicMock
import csv
from io import StringIO
from click.testing import CliRunner
from pdd.cli import cli  # Import the CLI application

@pytest.fixture
def runner() -> CliRunner:
    """Fixture to provide a Click CLI runner for testing."""
    return CliRunner()

def test_cli_version(runner: CliRunner) -> None:
    """Test the CLI version command."""
    result = runner.invoke(cli, ['--version'])
    assert result.exit_code == 0
    assert '0.2.1' in result.output  # Updated version

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



@pytest.fixture
def mock_getsize():
    with patch('os.path.getsize', return_value=0) as mock:
        yield mock

@pytest.fixture
def mock_isfile():
    with patch('os.path.isfile', return_value=True) as mock:
        yield mock

def test_fix_command(runner: CliRunner, tmp_path) -> None:
    """Test the fix command of the CLI with --auto-submit option."""
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
                                     '--output-test', str(output_test), '--output-code', str(output_code), '--auto-submit'])
        assert result.exit_code == 0
        assert "Fixed unit test saved to:" in result.output
        assert "Fixed code saved to:" in result.output
        assert output_test.exists()
        assert output_code.exists()

def test_split_command(tmp_path) -> None:
    """Test the split command of the CLI."""
    runner = CliRunner()
    input_prompt = tmp_path / "input_prompt.txt"
    input_prompt.write_text("Generate a complex Python program")
    input_code = tmp_path / "input_code.py"
    input_code.write_text("def complex_function(): pass")
    example_code = tmp_path / "example_code.py"
    example_code.write_text("complex_function()")
    output_sub = tmp_path / "sub_prompt.txt"
    output_modified = tmp_path / "modified_prompt.txt"

    # Mock the split_func to avoid external API calls
    with patch('pdd.cli.split_func', return_value=('sub prompt content', 'modified prompt content', 0.0)):
        result = runner.invoke(cli, [
            'split',
            str(input_prompt),
            str(input_code),
            str(example_code),
            '--output-sub', str(output_sub),
            '--output-modified', str(output_modified)
        ])
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
def test_conflicts_command(runner, tmp_path):
    """Test the conflicts command of the CLI."""
    prompt1 = tmp_path / "prompt1.txt"
    prompt1.write_text("Generate a Python function to add two numbers")
    prompt2 = tmp_path / "prompt2.txt"
    prompt2.write_text("Generate a Python function to subtract two numbers")
    output_file = tmp_path / "conflicts_analysis.csv"

    # Mock the function that interacts with the LLM to return consistent results
    with patch('pdd.conflicts_main.conflicts_in_prompts', return_value=([{
        'prompt_name': 'prompt1.prompt',
        'change_instructions': 'Update prompt1.prompt to include more specific details about the addition function.'
    }, {
        'prompt_name': 'prompt2.prompt',
        'change_instructions': 'Modify prompt2.prompt to include error handling for subtraction.'
    }], 0.0, 'mock_model')):
        result = runner.invoke(cli, ['conflicts', str(prompt1), str(prompt2), '--output', str(output_file)])
        assert result.exit_code == 0, f"Command failed with error: {result.output}"
        assert "Conflict analysis completed successfully." in result.output
        assert "Results saved to:" in result.output
        assert output_file.exists()

        # Read and verify the CSV content
        with open(output_file, 'r') as f:
            content = f.read().strip()

        # Define the desired output
        desired_output = """prompt_name,change_instructions
prompt1.prompt,Update prompt1.prompt to include more specific details about the addition function.
prompt2.prompt,Modify prompt2.prompt to include error handling for subtraction."""

        # Assert content matches the desired output
        assert content == desired_output, f"Output content does not match. Expected:\n{desired_output}\n\nGot:\n{content}"

def test_conflicts_command_csv():
    """
    Test the `conflicts` command of the PDD CLI with cost tracking.
    """
    runner = CliRunner()
    with runner.isolated_filesystem():
        # Create mock prompt files
        with open('prompt1.prompt', 'w') as f:
            f.write("Test prompt 1")
        with open('prompt2.prompt', 'w') as f:
            f.write("Test prompt 2")

        # Mock the conflicts_in_prompts function to return expected results
        with patch('pdd.conflicts_main.conflicts_in_prompts', return_value=([{
            'prompt_name': 'prompt1.prompt',
            'change_instructions': 'Update prompt1.prompt with additional context.'
        }, {
            'prompt_name': 'prompt2.prompt',
            'change_instructions': 'Modify prompt2.prompt to better align with the project goals.'
        }], 0.0, 'mock_model')):
            # Run the conflicts command with necessary options
            result = runner.invoke(cli, [
                '--force',
                '--strength', '0.7',
                '--temperature', '0.3',
                '--verbose',
                '--output-cost', 'cost.csv',
                'conflicts',
                '--output', 'conflicts_analysis.csv',
                'prompt1.prompt',
                'prompt2.prompt'
            ])

            # Assert command execution success
            assert result.exit_code == 0, f"Command failed with error: {result.output}"

            # Check if the output file was created
            assert os.path.exists('conflicts_analysis.csv'), "Output file was not created"

            # Read the content of the output file
            with open('conflicts_analysis.csv', 'r') as f:
                content = f.read().strip()

            # Define the desired output
            desired_output = """prompt_name,change_instructions
prompt1.prompt,Update prompt1.prompt with additional context.
prompt2.prompt,Modify prompt2.prompt to better align with the project goals."""

            # Assert content matches the desired output
            assert content == desired_output, f"Output content does not match. Expected:\n{desired_output}\n\nGot:\n{content}"

            # Check if the cost file was created and has the correct format
            assert os.path.exists('cost.csv'), "Cost file was not created"

            with open('cost.csv', 'r') as f:
                csv_reader = csv.DictReader(f)
                rows = list(csv_reader)
                assert len(rows) == 1, "Cost file should contain one data row"
                row = rows[0]
                assert set(row.keys()) == {'timestamp', 'model', 'command', 'cost', 'input_files', 'output_files'}, "Cost file has incorrect columns"
                assert row['command'] == 'conflicts', "Incorrect command in cost file"
                assert float(row['cost']) == 0.0, "Cost should be zero in mock"
                assert row['input_files'] == 'prompt1.prompt;prompt2.prompt', "Input files not correctly recorded"
                assert 'conflicts_analysis.csv' in row['output_files'], "Output file not correctly recorded"

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
    from unittest.mock import patch

    with runner.isolated_filesystem() as fs:
        home_dir = os.path.join(fs, "home", "user")
        os.makedirs(home_dir)
        bashrc_file = os.path.join(home_dir, ".bashrc")
        with open(bashrc_file, 'w') as f:
            f.write("# Existing content")

        # Mock environment variables and shell detection
        with patch.dict(os.environ, {'HOME': home_dir, 'SHELL': '/bin/bash'}):
            result = runner.invoke(cli, ['install-completion'])
        
        # Assert successful execution
        assert result.exit_code == 0
        assert "Shell completion installed for bash" in result.output
        
        # Verify that the completion command was appended correctly
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


@patch('os.path.isfile', return_value=True)
@patch('os.path.getsize', return_value=0)
def test_track_cost_decorator(mock_getsize, mock_isfile, runner: CliRunner, tmp_path):
    prompt_file = tmp_path / "test_prompt.txt"
    prompt_file.write_text("Generate a Python function to add two numbers")
    output_file = tmp_path / "output.py"
    cost_file = tmp_path / "cost.csv"

    # Mock the necessary functions
    mock_construct_paths = MagicMock(return_value=(
        {'prompt_file': 'mocked_prompt_content'},
        {'output': str(output_file)},
        'python'
    ))
    mock_code_generator = MagicMock(return_value=('def add(a, b): return a + b', 0.05, 'mock_model'))

    csv_output = StringIO()
    mock_csv_writer = MagicMock()

    with patch('pdd.cli.construct_paths', mock_construct_paths), \
         patch('pdd.cli.code_generator', mock_code_generator), \
         patch('builtins.open', mock_open()) as mock_file, \
         patch('csv.writer', return_value=mock_csv_writer):
        
        mock_file.return_value.__enter__.return_value = csv_output
        
        result = runner.invoke(cli, ['--output-cost', str(cost_file), 'generate', str(prompt_file), '--output', str(output_file)])
        
        # Check if the command executed successfully
        assert result.exit_code == 0, f"Command failed with error: {result.exception}"

        # Verify that the mocked functions were called
        mock_construct_paths.assert_called_once()
        mock_code_generator.assert_called_once()

        # Verify that the CSV writer was called with the correct data
        mock_csv_writer.writerow.assert_called()
        csv_data = list(mock_csv_writer.writerow.call_args[0][0])
        assert len(csv_data) == 6  # Verify that all 6 columns are present
        assert csv_data[1] == 'mock_model'
        assert csv_data[2] == 'generate'
        assert str(prompt_file) in csv_data[4]
        assert str(output_file) in csv_data[5]

    # Verify that the output file was created
    assert os.path.isfile(str(output_file))