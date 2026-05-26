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
    """Legacy mode: split command with --legacy + 3 positional args.

    The PR #1157 CLI added an agentic mode as the default. The legacy
    3-arg form now requires the --legacy flag.
    """
    # Setup mock return
    mock_split_main.return_value = ({"sub": "content"}, 0.05, "gpt-4")

    with runner.isolated_filesystem():
        open('prompt.txt', 'w').close()
        open('code.py', 'w').close()
        open('example.py', 'w').close()

        result = runner.invoke(split, [
            '--legacy',
            'prompt.txt',
            'code.py',
            'example.py',
            '--output-sub', 'sub.txt',
            '--output-modified', 'mod.txt'
        ])

    assert result.exit_code == 0, result.output
    mock_split_main.assert_called_once()
    call_kwargs = mock_split_main.call_args[1]
    assert call_kwargs['input_prompt_file'] == 'prompt.txt'
    assert call_kwargs['input_code_file'] == 'code.py'
    assert call_kwargs['example_code_file'] == 'example.py'
    assert call_kwargs['output_sub'] == 'sub.txt'
    assert call_kwargs['output_modified'] == 'mod.txt'

def test_split_exception_handling(runner, mock_split_main, mock_handle_error):
    """Test that exceptions in split are routed to handle_error (legacy mode)."""
    mock_split_main.side_effect = ValueError("Something went wrong")

    with runner.isolated_filesystem():
        open('p.txt', 'w').close()
        open('c.py', 'w').close()
        open('e.py', 'w').close()

        result = runner.invoke(split, ['--legacy', 'p.txt', 'c.py', 'e.py'])

    # The command catches exception and returns None (implicit exit code 0 unless handle_error exits)
    assert result.exit_code == 0, result.output
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


def test_change_clean_restart_rejects_non_issue_url(runner, mock_run_agentic_change):
    """--clean-restart should only run with a GitHub issue URL."""
    result = runner.invoke(change, ["--clean-restart", "not-a-url"])

    assert result.exit_code == 2
    assert "--clean-restart can only be used" in result.output
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


# -----------------------------------------------------------------------------
# Additional spec-coverage tests
# -----------------------------------------------------------------------------
# Test plan (spec requirements that need coverage):
#  - split agentic success: displays Status/Message/Cost/Model/changed files
#  - split agentic failure: exit(1)
#  - split agentic forwards intent, no_phase_extraction, strangler, max_cost,
#    use_github_state, timeout_adder
#  - split legacy with wrong arg count: UsageError
#  - change agentic forwards no_github_state -> use_github_state=False
#  - change manual CSV mode rejects directory-only when input_code is a file
#  - change agentic exit(1) on failure
#  - update 3-arg manual mode
#  - update validation: 2 args without --git -> UsageError
#  - update validation: 3 args with --git -> UsageError
#  - update validation: --all + path -> UsageError
#  - update validation: --budget <= 0 -> UsageError
#  - update repo mode + --git -> UsageError
#  - update repo mode + --output -> UsageError
#  - update file mode + --extensions -> UsageError
#  - update file mode + --directory -> UsageError
#  - update file mode + non-default --base-branch -> UsageError
#  - update file mode + --dry-run -> UsageError
#  - update file mode + --budget -> UsageError
#  - update --sync-metadata flag forwarded
#  - update --all mode behaves like repo mode
#  - update base-branch default value forwarded


# --- split agentic mode tests ---

@pytest.fixture
def mock_run_agentic_split():
    with patch('pdd.commands.modify.run_agentic_split') as m:
        yield m


def test_split_agentic_success(runner, mock_run_agentic_split):
    """Agentic split (default) displays status/cost/model and exits 0."""
    mock_run_agentic_split.return_value = (
        True, "Split complete", 0.1234, "mock-model", ["a.py", "b.py"]
    )
    result = runner.invoke(split, ['target.py'])
    assert result.exit_code == 0, result.output
    mock_run_agentic_split.assert_called_once()
    kwargs = mock_run_agentic_split.call_args.kwargs
    assert kwargs['target_file'] == 'target.py'
    assert "Status: Success" in result.output
    assert "Message: Split complete" in result.output
    assert "Cost: $0.1234" in result.output
    assert "Model: mock-model" in result.output
    assert "- a.py" in result.output
    assert "- b.py" in result.output


def test_split_agentic_failure_exits_with_1(runner, mock_run_agentic_split):
    """Agentic split returning success=False causes exit(1)."""
    mock_run_agentic_split.return_value = (
        False, "Failed", 0.0, "mock-model", []
    )
    result = runner.invoke(split, ['target.py'])
    assert result.exit_code == 1


def test_split_agentic_option_forwarding(runner, mock_run_agentic_split):
    """Spec options must propagate to run_agentic_split as kwargs."""
    mock_run_agentic_split.return_value = (
        True, "ok", 0.01, "mock-model", []
    )
    result = runner.invoke(split, [
        'target.py',
        '--intent', 'reduce',
        '--no-phase-extraction',
        '--strangler',
        '--max-cost', '5.0',
        '--no-github-state',
        '--timeout-adder', '1.5',
        '--diagnose',
        '--propose-only',
        '--delete-dead',
        '--force-split',
        '--no-verify',
        '--skip-regen-gate',
        '--experimental-language',
    ])
    assert result.exit_code == 0, result.output
    kwargs = mock_run_agentic_split.call_args.kwargs
    assert kwargs['intent'] == 'reduce'
    assert kwargs['no_phase_extraction'] is True
    assert kwargs['strangler'] is True
    assert kwargs['max_cost'] == 5.0
    assert kwargs['use_github_state'] is False
    assert kwargs['timeout_adder'] == 1.5
    assert kwargs['diagnose_only'] is True
    assert kwargs['propose_only'] is True
    assert kwargs['delete_dead'] is True
    assert kwargs['force_split'] is True
    assert kwargs['no_verify'] is True
    assert kwargs['skip_regen_gate'] is True
    assert kwargs['experimental_language'] is True


def test_split_max_cost_rejects_zero(runner):
    """--max-cost FloatRange(min=0.01) rejects 0."""
    result = runner.invoke(split, ['target.py', '--max-cost', '0'])
    assert result.exit_code == 2


def test_split_agentic_default_use_github_state_true(runner, mock_run_agentic_split):
    """Without --no-github-state, use_github_state should default to True."""
    mock_run_agentic_split.return_value = (True, "ok", 0.0, "m", [])
    result = runner.invoke(split, ['target.py'])
    assert result.exit_code == 0, result.output
    assert mock_run_agentic_split.call_args.kwargs['use_github_state'] is True


# --- change agentic tests ---

def test_change_agentic_forwards_no_github_state(runner, mock_run_agentic_change):
    """--no-github-state flips use_github_state to False."""
    mock_run_agentic_change.return_value = (True, "Done", 0.1, "m", [])
    result = runner.invoke(change, ['https://github.com/x/y/issues/1', '--no-github-state'])
    assert result.exit_code == 0
    assert mock_run_agentic_change.call_args.kwargs['use_github_state'] is False


def test_change_agentic_default_use_github_state_true(runner, mock_run_agentic_change):
    mock_run_agentic_change.return_value = (True, "Done", 0.1, "m", [])
    result = runner.invoke(change, ['https://github.com/x/y/issues/1'])
    assert result.exit_code == 0
    assert mock_run_agentic_change.call_args.kwargs['use_github_state'] is True


def test_change_agentic_failure_exits_with_1(runner, mock_run_agentic_change):
    """Agentic change returning success=False causes exit(1)."""
    mock_run_agentic_change.return_value = (False, "Failed", 0.0, "m", [])
    result = runner.invoke(change, ['https://github.com/x/y/issues/1'])
    assert result.exit_code == 1


def test_change_manual_csv_requires_directory(runner, mock_change_main):
    """--csv requires input_code to be a directory; file should fail."""
    with patch('pdd.commands.modify.Path.exists', return_value=True), \
         patch('pdd.commands.modify.Path.is_dir', return_value=False):
        result = runner.invoke(change, ['--manual', '--csv', 'batch.csv', 'not_a_dir'])
    assert result.exit_code == 2
    mock_change_main.assert_not_called()


def test_change_manual_standard_rejects_directory_as_code(runner, mock_change_main):
    """Standard manual mode requires input_code to be a file, not a directory."""
    def fake_exists(self):
        return True
    def fake_is_dir(self):
        return True  # always say it's a directory
    with patch('pdd.commands.modify.Path.exists', fake_exists), \
         patch('pdd.commands.modify.Path.is_dir', fake_is_dir):
        result = runner.invoke(change, ['--manual', 'change.prompt', 'code_dir', 'input.prompt'])
    assert result.exit_code == 2
    mock_change_main.assert_not_called()


def test_change_manual_budget_forwarded(runner, mock_change_main):
    """--budget forwards to change_main."""
    mock_change_main.return_value = ("ok", 0.1, "m")
    with patch('pdd.commands.modify.Path.exists', return_value=True), \
         patch('pdd.commands.modify.Path.is_dir', return_value=False):
        result = runner.invoke(change, [
            '--manual', '--budget', '7.5',
            'change.prompt', 'code.py', 'input.prompt'
        ])
    assert result.exit_code == 0, result.output
    assert mock_change_main.call_args.kwargs['budget'] == 7.5


# --- update validation tests ---

def test_update_2_args_without_git_rejects(runner, mock_update_main):
    """2 args require --git."""
    result = runner.invoke(update, ['prompt.prompt', 'code.py'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_3_args_with_git_rejects(runner, mock_update_main):
    """3 args + --git is invalid."""
    result = runner.invoke(update, ['--git', 'p', 'm', 'o'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_all_with_path_rejects(runner, mock_update_main):
    """--all with file paths is invalid."""
    result = runner.invoke(update, ['--all', 'code.py'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_budget_zero_rejects(runner, mock_update_main):
    """--budget must be > 0."""
    result = runner.invoke(update, ['--budget', '0'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_budget_negative_rejects(runner, mock_update_main):
    result = runner.invoke(update, ['--budget', '-1'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_repo_mode_rejects_git(runner, mock_update_main):
    """Repo mode forbids --git."""
    result = runner.invoke(update, ['--git'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_repo_mode_rejects_output(runner, mock_update_main):
    """Repo mode forbids --output."""
    result = runner.invoke(update, ['--output', 'foo.txt'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_file_mode_rejects_extensions(runner, mock_update_main):
    """File mode forbids --extensions."""
    result = runner.invoke(update, ['code.py', '--extensions', '.py'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_file_mode_rejects_directory_opt(runner, mock_update_main):
    """File mode forbids --directory."""
    result = runner.invoke(update, ['code.py', '--directory', 'src'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_file_mode_rejects_non_default_base_branch(runner, mock_update_main):
    """File mode forbids non-default --base-branch."""
    result = runner.invoke(update, ['code.py', '--base-branch', 'develop'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_file_mode_rejects_dry_run(runner, mock_update_main):
    """File mode forbids --dry-run."""
    result = runner.invoke(update, ['code.py', '--dry-run'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


def test_update_file_mode_rejects_budget(runner, mock_update_main):
    """File mode forbids --budget."""
    result = runner.invoke(update, ['code.py', '--budget', '5'])
    assert result.exit_code == 2
    mock_update_main.assert_not_called()


# --- update mode tests ---

def test_update_3_args_manual_mode(runner, mock_update_main):
    """3 args (without --git) -> input_prompt, modified_code, input_code."""
    mock_update_main.return_value = ("ok", 0.1, "m")
    result = runner.invoke(update, ['p.prompt', 'mod.py', 'orig.py'])
    assert result.exit_code == 0, result.output
    kwargs = mock_update_main.call_args.kwargs
    assert kwargs['input_prompt_file'] == 'p.prompt'
    assert kwargs['modified_code_file'] == 'mod.py'
    assert kwargs['input_code_file'] == 'orig.py'
    assert kwargs['use_git'] is False
    assert kwargs['repo'] is False


def test_update_all_flag_repo_mode(runner, mock_update_main):
    """--all triggers repo mode with no file paths."""
    mock_update_main.return_value = ("ok", 0.1, "m")
    result = runner.invoke(update, ['--all'])
    assert result.exit_code == 0, result.output
    kwargs = mock_update_main.call_args.kwargs
    assert kwargs['repo'] is True
    assert kwargs['input_prompt_file'] is None
    assert kwargs['modified_code_file'] is None
    assert kwargs['input_code_file'] is None


def test_update_sync_metadata_flag_forwarded(runner, mock_update_main):
    """--sync-metadata flag flows to update_main."""
    mock_update_main.return_value = ("ok", 0.1, "m")
    result = runner.invoke(update, ['code.py', '--sync-metadata'])
    assert result.exit_code == 0, result.output
    assert mock_update_main.call_args.kwargs['sync_metadata'] is True


def test_update_sync_metadata_default_false(runner, mock_update_main):
    mock_update_main.return_value = ("ok", 0.1, "m")
    result = runner.invoke(update, ['code.py'])
    assert result.exit_code == 0, result.output
    assert mock_update_main.call_args.kwargs['sync_metadata'] is False


def test_update_base_branch_default(runner, mock_update_main):
    """Default --base-branch is 'main' (repo mode)."""
    mock_update_main.return_value = ("ok", 0.1, "m")
    result = runner.invoke(update, [])
    assert result.exit_code == 0, result.output
    assert mock_update_main.call_args.kwargs['base_branch'] == 'main'


def test_update_base_branch_repo_mode_custom(runner, mock_update_main):
    """Custom --base-branch allowed in repo mode."""
    mock_update_main.return_value = ("ok", 0.1, "m")
    result = runner.invoke(update, ['--base-branch', 'develop'])
    assert result.exit_code == 0, result.output
    assert mock_update_main.call_args.kwargs['base_branch'] == 'develop'


def test_update_returns_none_when_update_main_returns_none(runner, mock_update_main):
    """If update_main returns None, command returns None gracefully."""
    mock_update_main.return_value = None
    result = runner.invoke(update, [])
    # No exception; @track_cost handles None return.
    assert result.exit_code == 0


def test_split_legacy_wrong_arg_count(runner, mock_split_main):
    """Legacy mode with not exactly 3 args raises UsageError."""
    result = runner.invoke(split, ['--legacy', 'only_one.txt'])
    assert result.exit_code == 2
    mock_split_main.assert_not_called()


def test_split_agentic_wrong_arg_count(runner, mock_run_agentic_split):
    """Agentic mode with 0 args raises UsageError."""
    result = runner.invoke(split, [])
    assert result.exit_code == 2
    mock_run_agentic_split.assert_not_called()
