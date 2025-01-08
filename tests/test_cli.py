import os
import pytest
from click.testing import CliRunner
from unittest.mock import patch

# Import the Click group from the module under test
# Adjust the import as needed if your code structure differs
from pdd.cli import cli, get_shell_rc_path

@pytest.fixture
def runner():
    """Returns a Click CliRunner instance."""
    return CliRunner()

def test_cli_no_command(runner):
    """Invoke the CLI with no command. Should display help and exit with code 0."""
    result = runner.invoke(cli, [])
    assert result.exit_code == 0
    assert "PDD (Prompt-Driven Development) Command Line Interface" in result.output
    assert "Commands:" in result.output

def test_cli_help_global(runner):
    """Invoke the CLI with --help. Should display general usage/help."""
    result = runner.invoke(cli, ["--help"])
    assert result.exit_code == 0
    assert "Usage:" in result.output
    assert "Options:" in result.output
    assert "--force" in result.output
    assert "Commands:" in result.output

def test_generate_command_missing_args(runner):
    """Test 'pdd generate' without required arguments. Should error and display help text."""
    result = runner.invoke(cli, ["generate"])
    assert result.exit_code != 0
    assert "Error: Missing argument 'PROMPT_FILE'" in result.output

def test_generate_command_help(runner):
    """Test 'pdd generate --help'. Should display usage for generate."""
    result = runner.invoke(cli, ["generate", "--help"])
    assert result.exit_code == 0
    assert "Create runnable code from a prompt file." in result.output
    assert "--output" in result.output

def test_example_command_missing_args(runner):
    """Test 'pdd example' without required arguments. Should error and display help text."""
    result = runner.invoke(cli, ["example"])
    assert result.exit_code != 0
    assert "Error: Missing argument 'PROMPT_FILE'" in result.output

def test_example_command_help(runner):
    """Test 'pdd example --help'. Should display usage for example."""
    result = runner.invoke(cli, ["example", "--help"])
    assert result.exit_code == 0
    assert "Create an example file from an existing code file" in result.output

def test_test_command_help(runner):
    """Test 'pdd test --help'. Should display usage for the test command."""
    result = runner.invoke(cli, ["test", "--help"])
    assert result.exit_code == 0
    assert "Generate or enhance unit tests" in result.output
    assert "--merge" in result.output
    assert "--coverage-report" in result.output

def test_preprocess_command_help(runner):
    """Test 'pdd preprocess --help'. Should display usage for the preprocess command."""
    result = runner.invoke(cli, ["preprocess", "--help"])
    assert result.exit_code == 0
    assert "Preprocess prompt files and save the results." in result.output
    assert "--xml" in result.output
    assert "--recursive" in result.output

def test_fix_command_help(runner):
    """Test 'pdd fix --help'. Should display usage for the fix command."""
    result = runner.invoke(cli, ["fix", "--help"])
    assert result.exit_code == 0
    assert "Fix errors in code and unit tests" in result.output
    assert "--loop" in result.output
    assert "--verification-program" in result.output

def test_split_command_help(runner):
    """Test 'pdd split --help'. Should display usage for the split command."""
    result = runner.invoke(cli, ["split", "--help"])
    assert result.exit_code == 0
    assert "Split large complex prompt files" in result.output
    assert "--output-sub" in result.output
    assert "--output-modified" in result.output

def test_change_command_help(runner):
    """Test 'pdd change --help'. Should display usage for the change command."""
    result = runner.invoke(cli, ["change", "--help"])
    assert result.exit_code == 0
    assert "Modify an input prompt file based on a change prompt" in result.output
    assert "--csv" in result.output

def test_update_command_help(runner):
    """Test 'pdd update --help'. Should display usage for the update command."""
    result = runner.invoke(cli, ["update", "--help"])
    assert result.exit_code == 0
    assert "Update the original prompt file based on the original code" in result.output
    assert "--git" in result.output

def test_detect_command_help(runner):
    """Test 'pdd detect --help'. Should display usage for the detect command."""
    result = runner.invoke(cli, ["detect", "--help"])
    assert result.exit_code == 0
    assert "Analyze a list of prompt files" in result.output

def test_conflicts_command_help(runner):
    """Test 'pdd conflicts --help'. Should display usage for the conflicts command."""
    result = runner.invoke(cli, ["conflicts", "--help"])
    assert result.exit_code == 0
    assert "Analyze two prompt files to find conflicts" in result.output

def test_crash_command_help(runner):
    """Test 'pdd crash --help'. Should display usage for the crash command."""
    result = runner.invoke(cli, ["crash", "--help"])
    assert result.exit_code == 0
    assert "Fix errors in a code module that caused a program to crash" in result.output
    assert "--loop" in result.output

def test_trace_command_help(runner):
    """Test 'pdd trace --help'. Should display usage for the trace command."""
    result = runner.invoke(cli, ["trace", "--help"])
    assert result.exit_code == 0
    assert "Find the associated line number between a prompt file and the generated code." in result.output

def test_bug_command_help(runner):
    """Test 'pdd bug --help'. Should display usage for the bug command."""
    result = runner.invoke(cli, ["bug", "--help"])
    assert result.exit_code == 0
    assert "Generate a unit test based on observed and desired outputs" in result.output

def test_auto_deps_command_help(runner):
    """Test 'pdd auto_deps --help'. Should display usage for the auto_deps command."""
    result = runner.invoke(cli, ["auto-deps", "--help"])
    assert result.exit_code == 0
    assert "Analyze a prompt file and a directory of potential dependencies" in result.output

def test_install_completion_unsupported_shell(runner):
    """
    Test 'pdd install_completion' with an unsupported shell by mocking $SHELL environment
    to a known unsupported shell (e.g., 'someothershell').
    We expect a failure with exit code 1.
    """
    with patch.dict(os.environ, {"SHELL": "/bin/someothershell"}):
        result = runner.invoke(cli, ["install_completion"])
        assert result.exit_code == 1
        assert "Unsupported shell" in result.output

def test_install_completion_fish_shell(runner, tmp_path):
    """
    Test 'pdd install_completion' with fish shell by mocking $SHELL environment to 'fish'
    and placing the fish completion script exactly where the CLI code expects it.
    """
    # Instead of putting pdd_completion.fish in tmp_path/pdd/, we designate
    # the entire pdd subdirectory as our PDD_PATH.
    mock_pdd_path = tmp_path / "pdd"
    os.makedirs(mock_pdd_path)

    completion_script_fish = os.path.join(str(mock_pdd_path), "pdd_completion.fish")
    with open(completion_script_fish, "w") as f:
        f.write("# fish completion script")

    # Now we patch the environment so that PDD_PATH=mock_pdd_path,
    # matching where we saved pdd_completion.fish
    with patch.dict(os.environ, {"SHELL": "/bin/fish", "PDD_PATH": str(mock_pdd_path)}):
        mock_rc_file = os.path.join(str(tmp_path), "config.fish")
        mock_rc_dir = os.path.dirname(mock_rc_file)
        os.makedirs(mock_rc_dir, exist_ok=True)
        with open(mock_rc_file, "w") as rc:
            rc.write("# fish config\n")

        # We still patch get_shell_rc_path to return mock_rc_file for fish.
        def mock_rc_path(shell: str):
            return mock_rc_file if shell == "fish" else None

        # Capture a reference to the real os.path.exists to avoid recursion
        real_exists = os.path.exists

        def safe_exists(path):
            # Return True if path is the fish script or the fish RC directory,
            # else call the real os.path.exists
            if path == completion_script_fish or path == mock_rc_dir:
                return True
            return real_exists(path)

        with patch("pdd.cli.get_shell_rc_path", side_effect=mock_rc_path), \
             patch("os.path.exists", side_effect=safe_exists):
            result = runner.invoke(cli, ["install_completion"])
            assert result.exit_code == 0, f"Expected exit_code 0 but got {result.exit_code}"
            assert "Shell completion installed for fish." in result.output

            # Confirm that the source command for our local script was appended
            with open(mock_rc_file, "r") as rc:
                contents = rc.read()
                assert f"source {completion_script_fish}" in contents

def test_get_shell_rc_path():
    """Verify that get_shell_rc_path returns expected defaults for known shells."""
    home = os.path.expanduser("~")

    assert get_shell_rc_path("bash") == os.path.join(home, ".bashrc")
    assert get_shell_rc_path("zsh") == os.path.join(home, ".zshrc")
    assert get_shell_rc_path("fish") == os.path.join(home, ".config", "fish", "config.fish")
    assert get_shell_rc_path("csh") is None

@pytest.mark.parametrize(
    "command, required_args",
    [
        ("generate", ["PROMPT_FILE"]),
        ("example", ["PROMPT_FILE", "CODE_FILE"]),
        ("test", ["PROMPT_FILE", "CODE_FILE"]),
        ("preprocess", ["PROMPT_FILE"]),
        ("fix", ["PROMPT_FILE", "CODE_FILE", "UNIT_TEST_FILE", "ERROR_FILE"]),
        ("split", ["INPUT_PROMPT", "INPUT_CODE", "EXAMPLE_CODE"]),
        ("change", ["CHANGE_PROMPT_FILE", "INPUT_CODE"]),
        ("update", ["INPUT_PROMPT_FILE", "MODIFIED_CODE_FILE"]),
        ("detect", ["PROMPT_FILES", "CHANGE_FILE"]),
        ("conflicts", ["PROMPT1", "PROMPT2"]),
        ("crash", ["PROMPT_FILE", "CODE_FILE", "PROGRAM_FILE", "ERROR_FILE"]),
        ("trace", ["PROMPT_FILE", "CODE_FILE", "CODE_LINE"]),
        ("bug", ["PROMPT_FILE", "CODE_FILE", "PROGRAM_FILE", "CURRENT_OUTPUT", "DESIRED_OUTPUT"]),
        ("auto-deps", ["PROMPT_FILE", "DIRECTORY_PATH"]),
    ],
)
def test_commands_with_no_args_give_error(runner, command, required_args):
    """
    Parametrized test to ensure commands that require arguments fail when none are provided,
    producing a missing argument error. This checks that the Click argument
    definitions are in place.
    """
    result = runner.invoke(cli, [command])
    assert result.exit_code != 0
    for arg in required_args:
        if arg == "PROMPT_FILES":
            continue
        assert f"Missing argument '{arg}'" in result.output or "Missing argument" in result.output, (
            f"Command '{command}' did not complain about missing arg '{arg}'. Output:\n{result.output}"
        )