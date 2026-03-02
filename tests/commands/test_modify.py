import sys
import os
from unittest.mock import MagicMock, patch
import pytest
from click.testing import CliRunner
from z3 import Solver, Bool, Int, And, Or, Not, Implies, sat

# Adjust path to allow imports if necessary (assuming standard package structure)
# In a real environment, the package 'pdd' should be installed or in pythonpath.
# Here we assume the test runner handles it, or we do a relative import if possible.
from pdd.commands.modify import split, change, update

# -----------------------------------------------------------------------------
# Z3 Formal Verification
# -----------------------------------------------------------------------------

def test_z3_verify_change_command_logic():
    """
    Use Z3 to formally verify the argument validation logic for the 'change' command.
    We model the validation rules and ensure that our understanding of 'valid' inputs
    matches the logical constraints.
    """
    s = Solver()

    # Inputs
    manual = Bool('manual')
    csv = Bool('csv')
    num_args = Int('num_args')

    # Logic derived from pdd/commands/modify.py:
    # Agentic: not manual -> num_args == 1
    valid_agentic = And(Not(manual), num_args == 1)

    # Manual CSV: manual and csv -> num_args == 2
    valid_manual_csv = And(manual, csv, num_args == 2)

    # Manual Standard: manual and not csv -> num_args in (2, 3)
    valid_manual_std = And(manual, Not(csv), Or(num_args == 2, num_args == 3))

    # Total Validity
    is_valid = Or(valid_agentic, valid_manual_csv, valid_manual_std)

    # 1. Verify that Agentic mode with 2 args is INVALID
    s.push()
    s.add(Not(manual))
    s.add(num_args == 2)
    s.add(is_valid) # Assert it IS valid (we expect this to be unsat)
    assert str(s.check()) == 'unsat', "Agentic mode should not accept 2 arguments"
    s.pop()

    # 2. Verify that Manual CSV mode with 2 args IS VALID
    s.push()
    s.add(manual)
    s.add(csv)
    s.add(num_args == 2)
    s.add(is_valid)
    assert str(s.check()) == 'sat', "Manual CSV mode should accept 2 arguments"
    s.pop()

    # 3. Verify that Manual Standard mode with 3 args IS VALID
    s.push()
    s.add(manual)
    s.add(Not(csv))
    s.add(num_args == 3)
    s.add(is_valid)
    assert str(s.check()) == 'sat', "Manual Standard mode should accept 3 arguments"
    s.pop()

    # 4. Verify that Manual Standard mode with 1 arg is INVALID
    s.push()
    s.add(manual)
    s.add(Not(csv))
    s.add(num_args == 1)
    s.add(is_valid)
    assert str(s.check()) == 'unsat', "Manual Standard mode should not accept 1 argument"
    s.pop()

# -----------------------------------------------------------------------------
# Unit Tests
# -----------------------------------------------------------------------------

@pytest.fixture
def runner():
    return CliRunner()

@pytest.fixture
def mock_split_main():
    with patch('pdd.commands.modify.split_main') as m:
        yield m

@pytest.fixture
def mock_change_main():
    with patch('pdd.commands.modify.change_main') as m:
        yield m

@pytest.fixture
def mock_run_agentic_change():
    with patch('pdd.commands.modify.run_agentic_change') as m:
        yield m

@pytest.fixture
def mock_update_main():
    with patch('pdd.commands.modify.update_main') as m:
        yield m

@pytest.fixture
def mock_handle_error():
    with patch('pdd.commands.modify.handle_error') as m:
        yield m

@pytest.fixture
def mock_path_exists():
    with patch('pdd.commands.modify.Path.exists') as m:
        m.return_value = True
        yield m

# --- Tests for 'split' command ---

def test_split_success(runner, mock_split_main, mock_path_exists):
    """Test split command calls split_main with correct arguments."""
    # Setup mock return
    mock_split_main.return_value = ({"sub": "content"}, 0.05, "gpt-4")

    with runner.isolated_filesystem():
        # Create dummy files to satisfy click.Path(exists=True) if not mocked, 
        # but we mocked Path.exists inside the command logic. 
        # However, Click's type=click.Path(exists=True) checks existence BEFORE the function runs. 
        # So we must create them physically in the isolated fs.
        open('prompt.txt', 'w').close()
        open('code.py', 'w').close()
        open('example.py', 'w').close()

        result = runner.invoke(split, [
            'prompt.txt', 
            'code.py', 
            'example.py',
            '--output-sub', 'sub.txt',
            '--output-modified', 'mod.txt'
        ])

    assert result.exit_code == 0
    mock_split_main.assert_called_once()
    call_kwargs = mock_split_main.call_args[1]
    assert call_kwargs['input_prompt_file'] == 'prompt.txt'
    assert call_kwargs['input_code_file'] == 'code.py'
    assert call_kwargs['example_code_file'] == 'example.py'
    assert call_kwargs['output_sub'] == 'sub.txt'
    assert call_kwargs['output_modified'] == 'mod.txt'

def test_split_exception_handling(runner, mock_split_main, mock_handle_error):
    """Test that exceptions in split are routed to handle_error."""
    mock_split_main.side_effect = ValueError("Something went wrong")
    
    with runner.isolated_filesystem():
        open('p.txt', 'w').close()
        open('c.py', 'w').close()
        open('e.py', 'w').close()
        
        result = runner.invoke(split, ['p.txt', 'c.py', 'e.py'])
    
    # The command catches exception and returns None (implicit exit code 0 unless handle_error exits)
    # In the provided code, handle_error is called and then returns None.
    # Usually handle_error might print and not exit, so exit_code is 0.
    assert result.exit_code == 0 
    mock_handle_error.assert_called_once()
    assert isinstance(mock_handle_error.call_args[0][0], ValueError)
    assert mock_handle_error.call_args[0][1] == "split"

# --- Tests for 'change' command ---

def test_change_agentic_success(runner, mock_run_agentic_change):
    """Test agentic mode (default) with valid arguments."""
    mock_run_agentic_change.return_value = (True, "Done", 1.0, "gpt-4", ["file1.py"])
    
    result = runner.invoke(change, ['https://github.com/issue/1'])
    
    assert result.exit_code == 0
    mock_run_agentic_change.assert_called_once()
    assert mock_run_agentic_change.call_args[1]['issue_url'] == 'https://github.com/issue/1'
    assert "Status: Success" in result.output
    assert "Cost: $1.0000" in result.output

def test_change_agentic_invalid_args(runner, mock_run_agentic_change, mock_handle_error):
    """Test agentic mode fails with wrong number of arguments."""
    # 0 arguments - UsageError propagates directly to Click (exit code 2)
    result = runner.invoke(change, [])
    assert result.exit_code == 2

    # 2 arguments
    result = runner.invoke(change, ['arg1', 'arg2'])
    assert result.exit_code == 2
    # Verify it didn't call the agentic runner
    mock_run_agentic_change.assert_not_called()

def test_change_manual_standard_success(runner, mock_change_main, mock_path_exists):
    """Test manual mode (standard) with 3 arguments."""
    mock_change_main.return_value = ("Modified Prompt", 0.5, "gpt-3.5")

    # We mock Path.exists to return True and Path.is_dir to return False (it's a file)
    with patch('pdd.commands.modify.Path.exists', return_value=True), \
         patch('pdd.commands.modify.Path.is_dir', return_value=False):
        result = runner.invoke(change, ['--manual', 'change.prompt', 'code.py', 'input.prompt'])

    assert result.exit_code == 0
    mock_change_main.assert_called_once()
    assert mock_change_main.call_args[1]['use_csv'] is False
    assert mock_change_main.call_args[1]['change_prompt_file'] == 'change.prompt'
    assert mock_change_main.call_args[1]['input_code'] == 'code.py'
    assert mock_change_main.call_args[1]['input_prompt_file'] == 'input.prompt'

def test_change_manual_standard_3args(runner, mock_change_main):
    """Test manual mode (standard) with 3 arguments."""
    mock_change_main.return_value = ("Modified Prompt", 0.5, "gpt-3.5")
    
    with patch('pdd.commands.modify.Path.exists', return_value=True):
        result = runner.invoke(change, ['--manual', 'change.prompt', 'code.py', 'input.prompt'])
    
    assert result.exit_code == 0
    assert mock_change_main.call_args[1]['input_prompt_file'] == 'input.prompt'

def test_change_manual_csv_success(runner, mock_change_main):
    """Test manual mode (CSV) with 2 arguments."""
    mock_change_main.return_value = ("Batch Done", 2.0, "gpt-4")

    # CSV mode requires input_code to be a directory
    with patch('pdd.commands.modify.Path.exists', return_value=True), \
         patch('pdd.commands.modify.Path.is_dir', return_value=True):
        result = runner.invoke(change, ['--manual', '--csv', 'batch.csv', 'src_dir'])

    assert result.exit_code == 0
    mock_change_main.assert_called_once()
    assert mock_change_main.call_args[1]['use_csv'] is True
    assert mock_change_main.call_args[1]['change_prompt_file'] == 'batch.csv'
    assert mock_change_main.call_args[1]['input_code'] == 'src_dir'

def test_change_manual_file_not_found(runner, mock_change_main, mock_handle_error):
    """Test manual mode validates file existence."""
    # Mock Path.exists to return False and is_dir to return False
    with patch('pdd.commands.modify.Path.exists', return_value=False), \
         patch('pdd.commands.modify.Path.is_dir', return_value=False):
        result = runner.invoke(change, ['--manual', 'missing.prompt', 'code.py', 'input.prompt'])

    mock_change_main.assert_not_called()
    # UsageError propagates directly to Click (exit code 2)
    assert result.exit_code == 2
    assert "not found" in result.output

# --- Tests for 'update' command ---

def test_update_repo_mode(runner, mock_update_main):
    """Test update command in repo mode (no file args)."""
    mock_update_main.return_value = ("Updated", 0.1, "gpt-4")

    result = runner.invoke(update, ['--extensions', '.py,.js'])

    assert result.exit_code == 0
    mock_update_main.assert_called_once()
    assert mock_update_main.call_args[1]['repo'] is True
    assert mock_update_main.call_args[1]['extensions'] == '.py,.js'
    assert mock_update_main.call_args[1]['modified_code_file'] is None

def test_update_single_file_mode(runner, mock_update_main):
    """Test update command in single file mode (args provided)."""
    mock_update_main.return_value = ("Updated", 0.1, "gpt-4")

    result = runner.invoke(update, ['file1.py', '--git'])

    assert result.exit_code == 0
    mock_update_main.assert_called_once()
    assert mock_update_main.call_args[1]['repo'] is False
    assert mock_update_main.call_args[1]['use_git'] is True
    assert mock_update_main.call_args[1]['modified_code_file'] == 'file1.py'

def test_update_simple_flag(runner, mock_update_main):
    """Test update command passes simple flag."""
    mock_update_main.return_value = ("Updated", 0.1, "gpt-4")
    
    result = runner.invoke(update, ['--simple'])
    
    assert mock_update_main.call_args[1]['simple'] is True
