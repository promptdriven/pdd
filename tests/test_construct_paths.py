# test_construct_paths.py

import pytest
from pathlib import Path
from unittest import mock
from unittest.mock import patch, MagicMock
import sys
import os

# Add the parent directory to sys.path to import pdd modules
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd.construct_paths import construct_paths

def test_construct_paths_load_input_files(tmpdir):
    """
    Test that construct_paths properly loads input files into input_strings,
    creates error_file if it doesn't exist, and handles missing input files.
    """

    # Create temporary input files
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    code_file = tmpdir.join('my_project.py')
    code_file.write('print("Hello World")')

    # Do not create error_file to test that it gets created
    error_file = tmpdir.join('errors.log')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    # Mock get_extension and get_language to return expected values
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

    # Assert input_strings contains the contents of the input files
    assert input_strings['prompt_file'] == 'Prompt content'
    assert input_strings['code_file'] == 'print("Hello World")'

    # The error_file should have been created
    assert Path(error_file).exists()

    # Assert the language is 'python'
    assert language == 'python'

def test_construct_paths_missing_input_file(tmpdir):
    """
    Test that construct_paths raises FileNotFoundError when a required input file is missing.
    """

    # Create only the prompt_file
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    # code_file does not exist
    code_file = tmpdir.join('my_project.py')

    error_file = tmpdir.join('errors.log')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with pytest.raises(FileNotFoundError) as excinfo:
        # Mock get_extension and get_language
        with patch('pdd.construct_paths.get_extension', return_value='.py'), \
             patch('pdd.construct_paths.get_language', return_value='python'), \
             patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):

            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )

    assert "Input file" in str(excinfo.value)

def test_construct_paths_error_file_creation(tmpdir):
    """
    Test that construct_paths creates the error_file if it does not exist.
    """

    # Create the required input files
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    code_file = tmpdir.join('my_project.py')
    code_file.write('print("Hello World")')

    # error_file does not exist
    error_file = tmpdir.join('errors.log')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = True
    quiet = False  # To see the warning message
    command = 'generate'
    command_options = {}

    with patch('pdd.construct_paths.rich_print') as mock_print, \
         patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Check that warning message is printed
        expected_warning = f"[yellow]Warning: Error file '{Path(error_file).resolve()}' does not exist. Creating an empty file.[/yellow]"
        mock_print.assert_any_call(expected_warning)

    # The error_file should have been created
    assert Path(error_file).exists()

def test_construct_paths_basename_extraction(tmpdir):
    """
    Test that construct_paths correctly extracts basename from input prompt files for different commands.
    """

    test_cases = [
        ('generate', 'my_project_python.prompt', 'my_project'),
        ('generate', 'my_project.prompt', 'my_project'),
        ('test', 'my_module_python.prompt', 'my_module'),
        ('split', 'large_project.prompt', 'large_project'),
        ('change', 'original_prompt_java.prompt', 'original_prompt'),
        ('detect', 'update_description.prompt', 'update_description'),
        ('conflicts', ('module1_python.prompt', 'module2_python.prompt'), 'module1_module2'),
        ('trace', 'trace_this_python.prompt', 'trace_this'),
    ]

    for case in test_cases:
        command = case[0]
        force = True
        quiet = True
        command_options = {}

        # Prepare input_file_paths based on command
        if command != 'conflicts':
            prompt_file_name = case[1]
            expected_basename = case[2]

            prompt_file = tmpdir.join(prompt_file_name)
            prompt_file.write('Prompt content')

            if command == 'split':
                input_file_paths = {'input_prompt': str(prompt_file)}
            elif command == 'change':
                input_file_paths = {'input_prompt_file': str(prompt_file)}
                command_options['csv'] = False
            elif command == 'detect':
                input_file_paths = {'change_file': str(prompt_file)}
            else:
                input_file_paths = {'prompt_file': str(prompt_file)}
        else:
            prompt_file_name1, prompt_file_name2 = case[1]
            expected_basename = case[2]

            prompt_file1 = tmpdir.join(prompt_file_name1)
            prompt_file1.write('Prompt content 1')

            prompt_file2 = tmpdir.join(prompt_file_name2)
            prompt_file2.write('Prompt content 2')

            input_file_paths = {
                'prompt1': str(prompt_file1),
                'prompt2': str(prompt_file2),
            }

        with patch('pdd.construct_paths.get_extension', return_value='.py'), \
             patch('pdd.construct_paths.get_language', return_value='python'), \
             patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:

            mock_generate_output_paths.return_value = {}
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )

            # Since we cannot access the internal 'basename' variable directly,
            # we can check that generate_output_paths was called with the expected basename
            mock_generate_output_paths.assert_called_with(
                command,
                {},
                expected_basename,
                mock.ANY,
                mock.ANY
            )

def test_construct_paths_language_extraction(tmpdir):
    """
    Test that construct_paths correctly extracts language from input prompt files and command options.
    """

    # Case when language is in prompt file name
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        assert language == 'python'

    # Case when language is in command_options
    prompt_file2 = tmpdir.join('my_project.prompt')
    prompt_file2.write('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file2)}
    command_options = {'language': 'javascript'}

    with patch('pdd.construct_paths.get_extension', return_value='.js'), \
         patch('pdd.construct_paths.get_language', return_value='javascript'), \
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        assert language == 'javascript'

    # Case when language is inferred from code_file extension
    code_file = tmpdir.join('my_project.js')
    code_file.write('console.log("Hello World");')

    input_file_paths = {
        'prompt_file': str(prompt_file2),
        'code_file': str(code_file)
    }
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value='.js'), \
         patch('pdd.construct_paths.get_language', return_value='javascript'), \
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        assert language == 'javascript'

    # Case when language cannot be determined
    input_file_paths = {'prompt_file': str(prompt_file2)}
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value=None), \
         patch('pdd.construct_paths.get_language', return_value=None):

        with pytest.raises(ValueError) as excinfo:
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )

        assert "Could not determine language" in str(excinfo.value)

def test_construct_paths_output_file_exists(tmpdir):
    """
    Test that construct_paths prompts the user when output files exist and 'force' is False.
    """

    # Create input files
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    code_file = tmpdir.join('my_project.py')
    code_file.write('print("Hello World")')

    error_file = tmpdir.join('errors.log')
    error_file.write('Error log')

    # Create an output file that already exists
    output_file = tmpdir.join('output.py')
    output_file.write('Existing output')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = False
    quiet = True
    command = 'generate'
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(output_file)}), \
         patch('rich.prompt.Confirm.ask', return_value=False) as mock_confirm, \
         patch('builtins.print'):

        with pytest.raises(SystemExit):
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )

        mock_confirm.assert_called_once()

    # Now test when user confirms overwrite
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(output_file)}), \
         patch('rich.prompt.Confirm.ask', return_value=True) as mock_confirm, \
         patch('builtins.print'):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        mock_confirm.assert_called_once()
        assert output_file_paths['output'] == str(output_file)

def test_construct_paths_quiet_flag(tmpdir, capsys):
    """
    Test that construct_paths prints input and output file paths when 'quiet' is False,
    and does not print when 'quiet' is True.
    """

    # Create input files
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    code_file = tmpdir.join('my_project.py')
    code_file.write('print("Hello World")')

    error_file = tmpdir.join('errors.log')
    error_file.write('Error log')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = True
    command = 'generate'
    command_options = {}

    # Test with quiet=False
    quiet = False

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        captured = capsys.readouterr()
        assert "Input file paths:" in captured.out
        assert "Output file paths:" in captured.out

    # Test with quiet=True
    quiet = True

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        captured = capsys.readouterr()
        # No output should be printed
        assert captured.out == ''
        

def test_construct_paths_invalid_command(tmpdir):
    """
    Test that construct_paths raises a ValueError when an invalid command is provided.
    """

    # Create input files
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'invalid_command'
    command_options = {}

    with pytest.raises(ValueError) as excinfo:
        with patch('pdd.construct_paths.get_extension', return_value='.py'), \
             patch('pdd.construct_paths.get_language', return_value='python'):
            construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
    assert "Invalid command" in str(excinfo.value)


def test_construct_paths_missing_command_options(tmpdir):
    """
    Test that construct_paths handles missing command options gracefully.
    """

    # Create input files
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = None  # Missing command options

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
        # Check that defaults are used and no exception is raised
        assert input_strings['prompt_file'] == 'Prompt content'
        assert language == 'python'


def test_construct_paths_unsupported_extension(tmpdir):
    """
    Test that construct_paths raises an error when the file extension is unsupported.
    """

    # Create input files with unsupported extension
    prompt_file = tmpdir.join('my_project.unsupported')
    prompt_file.write('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value='.unsupported'), \
         patch('pdd.construct_paths.get_language', return_value=None):
        with pytest.raises(ValueError) as excinfo:
            construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
        assert "Unsupported file extension" in str(excinfo.value)


def test_construct_paths_special_characters_in_filenames(tmpdir):
    """
    Test that construct_paths properly handles filenames with special characters.
    """

    # Create input files with special characters
    prompt_file = tmpdir.join('my_project @123!.prompt')
    prompt_file.write('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:
        mock_generate_output_paths.return_value = {'output': str(tmpdir.join('output.py'))}

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Check that the special characters are handled without errors
        assert input_strings['prompt_file'] == 'Prompt content'
        assert language == 'python'


def test_construct_paths_no_input_files(tmpdir):
    """
    Test that construct_paths raises an error when no input files are provided.
    """

    input_file_paths = {}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with pytest.raises(ValueError) as excinfo:
        construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    assert "No input files provided" in str(excinfo.value)


def test_construct_paths_conflicting_language_specification(tmpdir):
    """
    Test that construct_paths handles conflicting language specifications between filenames and command options.
    """

    # Language in filename is 'python'
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    # Language specified in command options is 'javascript'
    command_options = {'language': 'javascript'}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language') as mock_get_language, \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.js'))}):
        mock_get_language.return_value = 'javascript'

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Command option should take precedence
        assert language == 'javascript'
        assert output_file_paths['output'].endswith('.js')


def test_construct_paths_missing_error_file(tmpdir):
    """
    Test that construct_paths handles a missing error_file path correctly.
    """

    # Create input files
    prompt_file = tmpdir.join('my_project_python.prompt')
    prompt_file.write('Prompt content')
    code_file = tmpdir.join('my_project.py')
    code_file.write('print("Hello World")')

    # error_file path not provided
    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
    }
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
        # Check that construct_paths does not fail and handles missing error_file
        assert 'error_file' not in input_file_paths


def test_construct_paths_nonexistent_directory(tmpdir):
    """
    Test that construct_paths raises an error when provided file paths point to a nonexistent directory.
    """

    # Create a path that does not exist
    nonexistent_dir = tmpdir.join('nonexistent')
    prompt_file = nonexistent_dir.join('my_project_python.prompt')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with pytest.raises(FileNotFoundError) as excinfo:
        construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    assert "does not exist" in str(excinfo.value)


def test_construct_paths_relative_paths(tmpdir):
    """
    Test that construct_paths correctly handles relative file paths.
    """

    # Change the working directory to tmpdir
    with tmpdir.as_cwd():
        # Create input files with relative paths
        prompt_file = Path('my_project_python.prompt')
        prompt_file.write_text('Prompt content')

        input_file_paths = {'prompt_file': str(prompt_file)}
        force = True
        quiet = True
        command = 'generate'
        command_options = {}

        with patch('pdd.construct_paths.get_extension', return_value='.py'), \
             patch('pdd.construct_paths.get_language', return_value='python'), \
             patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
            # Check that files are correctly found and read
            assert input_strings['prompt_file'] == 'Prompt content'
            assert language == 'python'


def test_construct_paths_symbolic_links(tmpdir):
    """
    Test that construct_paths correctly resolves symbolic links in file paths.
    """

    # Create actual file
    real_prompt_file = tmpdir.join('real_my_project.prompt')
    real_prompt_file.write('Prompt content')

    # Create a symbolic link
    symlink_prompt_file = tmpdir.join('my_project.prompt')
    symlink_prompt_file.mksymlinkto(real_prompt_file)

    input_file_paths = {'prompt_file': str(symlink_prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value={'output': str(tmpdir.join('output.py'))}):
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
        # Check that the symlink is correctly resolved
        assert input_strings['prompt_file'] == 'Prompt content'
        assert language == 'python'

# Create dummy files for testing
@pytest.fixture(scope="module")
def setup_test_files(tmp_path_factory):
    """
    Fixture to set up test files for the tests.
    Creates temporary files and directories for testing purposes.
    """
    test_dir = tmp_path_factory.mktemp("test_files")

    # Create prompt files
    (test_dir / "unfinished_prompt_python.prompt").write_text("Test prompt content")
    (test_dir / "main_gen_LLM.prompt").write_text("Test prompt content")

    # Create code files
    (test_dir / "unfinished_prompt.py").write_text("def test_function():\n    pass")

    return test_dir

def test_construct_paths_example_command(setup_test_files):
    """
    Test the 'example' command of the construct_paths function.
    Verifies that the output file path and language are correctly generated.
    """
    input_file_paths = {
        "code_file": str(setup_test_files / "unfinished_prompt.py"),
        "prompt_file": str(setup_test_files / "unfinished_prompt_python.prompt")
    }
    command_options = {
        "output": None
    }

    input_strings, output_file_paths, language = construct_paths(
        input_file_paths=input_file_paths,
        force=True,
        quiet=True,
        command="example",
        command_options=command_options
    )

    assert language == "python"
    assert output_file_paths["output"] == str( "unfinished_prompt_example.py")

def test_construct_paths_generate_command(setup_test_files):
    """
    Test the 'generate' command of the construct_paths function.
    Verifies that the output file path and language are correctly generated.
    """
    input_file_paths = {
        "prompt_file": str(setup_test_files / "main_gen_LLM.prompt")
    }
    command_options = {
        "output": str(setup_test_files)
    }

    input_strings, output_file_paths, language = construct_paths(
        input_file_paths=input_file_paths,
        force=True,
        quiet=True,
        command="generate",
        command_options=command_options
    )

    assert language == "prompt"
    assert output_file_paths["output"] == str(setup_test_files / "main_gen.prompt")

def test_construct_paths_detects_incorrect_output_path(setup_test_files):
    """
    Test to identify the issue where an incorrect output path is generated for the 'generate' command.
    The desired output path should be 'main_gen_LLM.py' within the specified directory,
    but the current code incorrectly produces 'main_gen_LLM_.py'.
    """
    input_file_paths = {
        "prompt_file": str(setup_test_files / "main_gen_LLM.prompt")
    }
    command_options = {
        "output": str(setup_test_files)
    }

    _, output_file_paths, _ = construct_paths(
        input_file_paths=input_file_paths,
        force=True,
        quiet=True,
        command="generate",
        command_options=command_options
    )

    # The desired output path should not have an extra underscore
    desired_output_path = str(setup_test_files / "main_gen_LLM.py")
    assert output_file_paths["output"] == desired_output_path, f"Expected {desired_output_path}, but got {output_file_paths['output']}"