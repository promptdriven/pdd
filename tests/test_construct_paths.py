# test_construct_paths.py

import pytest
from pathlib import Path
from unittest import mock
from unittest.mock import patch, MagicMock, ANY
import sys
import os

# Add the parent directory to sys.path to import pdd modules
# Ensure this path is correct relative to where pytest is run
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# Mock generate_output_paths before importing construct_paths if it's needed globally
# Or mock within each test as currently done.

# Import after potentially modifying sys.path
from pdd.construct_paths import construct_paths

# Helper to create absolute path for comparison
def resolve_path(relative_path_str, base_dir):
    return str(Path(base_dir) / relative_path_str)

def test_construct_paths_load_input_files(tmpdir):
    """
    Test that construct_paths properly loads input files into input_strings,
    creates error_file if it doesn't exist, and handles missing input files.
    """
    tmp_path = Path(str(tmpdir))

    # Create temporary input files
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')

    code_file = tmp_path / 'my_project.py'
    code_file.write_text('print("Hello World")')

    # Do not create error_file to test that it gets created
    error_file = tmp_path / 'errors.log'

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = True
    quiet = True # Keep quiet True to avoid printing during test
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    # to match the likely cause of the verification error
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    # Mock get_extension and get_language to return expected values
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

    # Assert input_strings contains the contents of the input files
    assert input_strings['prompt_file'] == 'Prompt content'
    assert input_strings['code_file'] == 'print("Hello World")'
    # Error file should exist and be empty (or contain content if it existed before)
    assert error_file.exists()
    assert error_file.read_text() == "" # Check it's empty as it was created
    assert input_strings['error_file'] == "" # Check loaded content is empty

    # Assert the language is 'python'
    assert language == 'python'
    # Assert output paths are strings
    assert isinstance(output_file_paths['output'], str)
    assert output_file_paths['output'] == str(mock_output_path)


def test_construct_paths_missing_input_file(tmpdir):
    """
    Test that construct_paths raises FileNotFoundError when a required input file is missing.
    """
    tmp_path = Path(str(tmpdir))

    # Create only the prompt_file
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')

    # code_file does not exist
    code_file_str = str(tmp_path / 'my_project.py') # Path string, file doesn't exist

    error_file = tmp_path / 'errors.log'

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': code_file_str, # Pass path string even if it doesn't exist
        'error_file': str(error_file),
    }
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    with pytest.raises(FileNotFoundError) as excinfo:
        # Mock get_extension and get_language
        with patch('pdd.construct_paths.get_extension', return_value='.py'), \
             patch('pdd.construct_paths.get_language', return_value='python'), \
             patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

            construct_paths(
                input_file_paths, force, quiet, command, command_options
            )

    # Check if the path string is in the standard FileNotFoundError message
    # Note: The error message from resolve(strict=True) might just contain the path
    # or a more specific message depending on the OS/Python version.
    # Checking for the path string itself is generally reliable.
    assert code_file_str in str(excinfo.value)


def test_construct_paths_error_file_creation(tmpdir):
    """
    Test that construct_paths creates the error_file if it does not exist and warns when quiet=False.
    """
    tmp_path = Path(str(tmpdir))

    # Create the required input files
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')

    code_file = tmp_path / 'my_project.py'
    code_file.write_text('print("Hello World")')

    # error_file does not exist
    error_file = tmp_path / 'errors.log'

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = True
    quiet = False  # To see the warning message
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    with patch('pdd.construct_paths.console.print') as mock_print, \
         patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Check that warning message is printed for error file creation (less brittle check, no tags)
        warning_core_message = f"Warning: Error file '{error_file.resolve()}' does not exist. Creating an empty file."
        found_warning = any(warning_core_message in call_args[0] for call_args, call_kwargs in mock_print.call_args_list if call_args)
        assert found_warning, f"Expected warning containing '{warning_core_message}' not found in calls: {mock_print.call_args_list}"


    # The error_file should have been created
    assert error_file.exists()
    assert error_file.read_text() == ""


def test_construct_paths_basename_extraction(tmpdir):
    """
    Test that construct_paths correctly extracts basename from input prompt files for different commands.
    """
    tmp_path = Path(str(tmpdir))

    test_cases = [
        # command, input_dict_key, input_filename(s), expected_basename, expect_error
        ('generate', 'prompt_file', 'my_project_python.prompt', 'my_project', False),
        ('generate', 'prompt_file', 'my_project.prompt', 'my_project', True), # Expect error: No lang suffix
        ('test', 'prompt_file', 'my_module_python.prompt', 'my_module', False),
        ('split', 'input_prompt', 'large_project.prompt', 'large_project', True), # Expect error: No lang suffix
        # Change command basename depends on change_prompt_file if present
        ('change', 'change_prompt_file', 'how_to_change_original.prompt', 'how_to_change_original', True), # Expect error: No lang suffix/code file
        # Change command fallback if change_prompt_file absent (uses input_prompt_file)
        ('change', 'input_prompt_file', 'original_prompt_java.prompt', 'original_prompt', False),
        # Detect command now has special handling and defaults to 'prompt' language
        ('detect', 'change_file', 'update_description.prompt', 'update_description', False), # No longer expect error with special handling
        # Conflicts uses sorted combination
        ('conflicts', ('prompt1', 'prompt2'), ('module2_python.prompt', 'module1_python.prompt'), 'module1_module2', False),
        ('trace', 'prompt_file', 'trace_this_python.prompt', 'trace_this', False),
        # Case with no language suffix
        ('generate', 'prompt_file', 'no_lang.prompt', 'no_lang', True), # Expect error: No lang suffix
        # Case where prompt is not .prompt extension (should still work if key matches)
        ('generate', 'prompt_file', 'my_config_python.cfg', 'my_config', False),
    ]

    for case in test_cases:
        command, input_key, file_info, expected_basename, expect_error = case
        force = True
        quiet = True
        command_options = {}
        input_file_paths = {}
        dummy_code = None # Initialize dummy_code

        # Prepare input_file_paths based on command and file_info
        if isinstance(file_info, tuple): # Conflicts case
            key1, key2 = input_key
            filename1, filename2 = file_info
            file1 = tmp_path / filename1
            file1.write_text('Content 1')
            file2 = tmp_path / filename2
            file2.write_text('Content 2')
            input_file_paths = {key1: str(file1), key2: str(file2)}
        else: # Single file case
            filename = file_info
            file_path = tmp_path / filename
            file_path.write_text('Content')
            input_file_paths = {input_key: str(file_path)}
            # Add dummy code file if needed for language detection fallback (though mocked here)
            # Only add if not expecting an error and if needed
            if not expect_error and 'code_file' not in input_file_paths and command not in ['split', 'detect', 'conflicts', 'change']:
                 # Use expected_basename which should be correct after _strip_language_suffix fix
                 base_for_dummy = expected_basename
                 # Handle conflicts case where expected_basename is combined
                 if command == 'conflicts': base_for_dummy = 'dummy' # Avoid module1_module2.py
                 # Determine dummy extension based on expected language
                 dummy_ext = '.py' # Default
                 if '_java' in filename: dummy_ext = '.java'
                 elif '_python' in filename: dummy_ext = '.py'
                 elif '.cfg' in filename and '_python' in filename: dummy_ext = '.py' # Special case

                 dummy_code = tmp_path / f"{base_for_dummy}{dummy_ext}"
                 dummy_code.touch()
                 input_file_paths['code_file'] = str(dummy_code)


        # Mock generate_output_paths to return resolved Path objects as STRINGS
        mock_output_path = tmp_path / f'{expected_basename}_output.out'
        mock_output_paths_dict_str = {'output': str(mock_output_path)}

        # Determine expected language based on filename/command for mocking get_language
        # This is tricky because the test mocks get_language, but the internal logic might not call it as expected.
        # We set mocks based on what *should* happen if the language *could* be determined.
        determined_lang = 'python' # Default
        mock_ext = '.py'
        if not expect_error: # Only determine language if not expecting error
            if isinstance(file_info, str):
                if command == 'detect' and input_key == 'change_file':
                    # Special case for detect command
                    determined_lang = 'prompt'
                    mock_ext = ''
                elif '_python' in file_info: determined_lang = 'python'; mock_ext = '.py'
                elif '_java' in file_info: determined_lang = 'java'; mock_ext = '.java'
                elif '.cfg' in file_info and '_python' in file_info: determined_lang = 'python'; mock_ext = '.py' # From suffix
                elif command == 'change' and 'java' in file_info: determined_lang = 'java'; mock_ext = '.java'
                elif command == 'trace': determined_lang = 'python'; mock_ext = '.py'
                elif command == 'test': determined_lang = 'python'; mock_ext = '.py'
                # Other cases might rely on code_file if added
                elif 'code_file' in input_file_paths:
                    code_ext = Path(input_file_paths['code_file']).suffix
                    if code_ext == '.py': determined_lang = 'python'; mock_ext = '.py'
                    elif code_ext == '.java': determined_lang = 'java'; mock_ext = '.java'
                    # Add more if needed
            elif isinstance(file_info, tuple): # conflicts
                 # Assume python based on filenames in test case
                 determined_lang = 'python'; mock_ext = '.py'
        else:
            # If expecting error, mocks might not matter as much, but set defaults
            determined_lang = None
            mock_ext = ''


        # Dynamic get_extension mock for _strip_language_suffix
        def dynamic_get_extension(lang_candidate):
            if lang_candidate == 'python': return '.py'
            if lang_candidate == 'java': return '.java'
            # Add other known languages if needed by test cases
            return '' # Default for unknown

        if expect_error:
            # Expect ValueError("Could not determine language...")
            with pytest.raises(ValueError) as excinfo:
                 with patch('pdd.construct_paths.get_extension', side_effect=dynamic_get_extension), \
                      patch('pdd.construct_paths.get_language', return_value=None), \
                      patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
                      construct_paths(
                          input_file_paths, force, quiet, command, command_options
                      )
            assert "Could not determine language" in str(excinfo.value), f"Case {case} failed"
        else:
            # Expect success
            with patch('pdd.construct_paths.get_extension', side_effect=dynamic_get_extension) as mock_get_ext, \
                 patch('pdd.construct_paths.get_language', return_value=determined_lang), \
                 patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:

                mock_generate_output_paths.return_value = mock_output_paths_dict_str
                try:
                    input_strings, output_file_paths, language = construct_paths(
                        input_file_paths, force, quiet, command, command_options
                    )
                except ValueError as e:
                    pytest.fail(f"construct_paths raised unexpected ValueError for case {case}: {e}")
                except FileNotFoundError as e:
                     pytest.fail(f"construct_paths raised unexpected FileNotFoundError for case {case}: {e}")


                # Check that generate_output_paths was called with the expected basename using keyword args
                # The language/extension passed should match the determined ones
                mock_generate_output_paths.assert_called_once_with(
                    command=command,
                    output_locations={}, # Filtered options
                    basename=expected_basename,
                    language=determined_lang, # Use the language determined for mocking
                    file_extension=mock_ext # Use the extension determined for mocking
                )
        # Clean up dummy code file
        if dummy_code and dummy_code.exists():
            dummy_code.unlink()


def test_construct_paths_language_extraction(tmpdir):
    """
    Test that construct_paths correctly extracts language from input prompt files and command options.
    """
    tmp_path = Path(str(tmpdir))

    # Mock generate_output_paths globally for this test to return STRINGS
    mock_output_path = tmp_path / 'output.file'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    # Case 1: Language in prompt file name (my_project_python.prompt)
    prompt_file_py = tmp_path / 'my_project_python.prompt'
    prompt_file_py.write_text('Prompt content')
    input_file_paths_1 = {'prompt_file': str(prompt_file_py)}
    command_options_1 = {}
    # Mocks should reflect the *expected internal calls* for this case
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        _, _, language1 = construct_paths(input_file_paths_1, True, True, 'generate', command_options_1)
        assert language1 == 'python'

    # Case 2: Language in command_options (overrides filename if different)
    prompt_file_generic = tmp_path / 'my_project.prompt' # No suffix
    prompt_file_generic.write_text('Prompt content')
    input_file_paths_2 = {'prompt_file': str(prompt_file_generic)}
    command_options_2 = {'language': 'javascript'} # Explicit language
    # Mocks reflect the *explicitly chosen* language
    with patch('pdd.construct_paths.get_extension', return_value='.js'), \
         patch('pdd.construct_paths.get_language', return_value='javascript'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        _, _, language2 = construct_paths(input_file_paths_2, True, True, 'generate', command_options_2)
        assert language2 == 'javascript'

    # Case 3: Language inferred from code_file extension (when not explicit or in prompt name)
    code_file_js = tmp_path / 'my_project.js'
    code_file_js.write_text('console.log("Hello World");')
    input_file_paths_3 = {'prompt_file': str(prompt_file_generic), 'code_file': str(code_file_js)}
    command_options_3 = {}
    # Mock get_language to return js for .js, and None otherwise to test priority
    def mock_get_language_func_case3(ext_or_name):
        if ext_or_name == '.js': return 'javascript'
        return None # Simulate no language for .prompt or other files
    # Mock get_extension to return .js when language is javascript
    def mock_get_extension_func_case3(lang):
         if lang == 'javascript': return '.js'
         return ''
    with patch('pdd.construct_paths.get_extension', side_effect=mock_get_extension_func_case3), \
         patch('pdd.construct_paths.get_language', side_effect=mock_get_language_func_case3), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        _, _, language3 = construct_paths(input_file_paths_3, True, True, 'generate', command_options_3)
        assert language3 == 'javascript' # Should prioritize .js over .prompt

    # Case 4: Language cannot be determined (no explicit, no code file, generic prompt name)
    input_file_paths_4 = {'prompt_file': str(prompt_file_generic)}
    command_options_4 = {}
    # Mock get_language to return None for all inputs
    def dynamic_get_ext_case4(lang): return "" # Always return ""
    with patch('pdd.construct_paths.get_extension', side_effect=dynamic_get_ext_case4), \
         patch('pdd.construct_paths.get_language', return_value=None), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        with pytest.raises(ValueError) as excinfo:
            construct_paths(input_file_paths_4, True, True, 'generate', command_options_4)
        assert "Could not determine language" in str(excinfo.value)

    # Case 5: Language inferred from Makefile (no extension)
    makefile = tmp_path / 'Makefile'
    makefile.write_text('all: build')
    input_file_paths_5 = {'build_script': str(makefile)} # Use a generic key
    command_options_5 = {}
    # Mock get_language to return 'makefile' for 'Makefile' name
    def mock_get_language_func_case5(ext_or_name):
        if ext_or_name == 'Makefile': return 'makefile'
        return None
    # Mock get_extension for makefile
    def mock_get_extension_func_case5(lang):
         if lang == 'makefile': return '' # Or 'Makefile' depending on get_extension impl
         return ''
    with patch('pdd.construct_paths.get_extension', side_effect=mock_get_extension_func_case5), \
         patch('pdd.construct_paths.get_language', side_effect=mock_get_language_func_case5), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
         # Need a basename source - add generic prompt
         input_file_paths_5['prompt_file'] = str(prompt_file_generic)
         # Need language source for generate_output_paths call - rely on Makefile
         _, _, language5 = construct_paths(input_file_paths_5, True, True, 'generate', command_options_5)
         assert language5 == 'makefile'


def test_construct_paths_output_file_exists(tmpdir):
    """
    Test that construct_paths prompts the user when output files exist and 'force' is False.
    """
    tmp_path = Path(str(tmpdir))

    # Create input files
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')
    code_file = tmp_path / 'my_project.py'
    code_file.write_text('print("Hello World")')
    error_file = tmp_path / 'errors.log'
    error_file.write_text('Error log')

    # Create an output file that already exists
    output_file = tmp_path / 'output.py'
    output_file.write_text('Existing output')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = False
    quiet = False # Set quiet=False to see the warning print
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_paths_dict_str = {'output': str(output_file)}

    # Test when user cancels (returns False)
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str), \
         patch('click.confirm', return_value=False) as mock_confirm, \
         patch('click.secho') as mock_secho, \
         patch('pdd.construct_paths.console.print') as mock_print: # Patch console print too

        with pytest.raises(SystemExit) as excinfo:
            construct_paths(
                input_file_paths, force, quiet, command, command_options
            )

        assert excinfo.value.code == 1
        mock_confirm.assert_called_once()
        # Check confirmation message style (optional, can be brittle)
        # assert mock_confirm.call_args[0][0].startswith(click.style("Overwrite existing files?", fg="yellow"))
        mock_secho.assert_called_with("Operation cancelled.", fg="red", err=True)
        # Check that the warning about existing files was printed (less brittle, no tags)
        overwrite_core_message = "Warning: The following output files already exist and may be overwritten:"
        found_warning = any(overwrite_core_message in call_args[0] for call_args, call_kwargs in mock_print.call_args_list if call_args)
        assert found_warning, f"Expected warning containing '{overwrite_core_message}' not found in calls: {mock_print.call_args_list}"
        found_path = any(str(output_file.resolve()) in call_args[0] for call_args, call_kwargs in mock_print.call_args_list if call_args)
        assert found_path, f"Expected path '{output_file.resolve()}' not found in warning calls: {mock_print.call_args_list}"


    # Test when user confirms overwrite (returns True)
    # Reset mocks for the second part of the test
    mock_confirm.reset_mock()
    mock_secho.reset_mock()
    mock_print.reset_mock()

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str), \
         patch('click.confirm', return_value=True) as mock_confirm, \
         patch('click.secho') as mock_secho, \
         patch('pdd.construct_paths.console.print') as mock_print:

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        mock_confirm.assert_called_once()
        mock_secho.assert_not_called() # Should not print cancellation message
        assert output_file_paths['output'] == str(output_file)
        # Check that the warning about existing files was printed (less brittle, no tags)
        overwrite_core_message = "Warning: The following output files already exist and may be overwritten:"
        found_warning = any(overwrite_core_message in call_args[0] for call_args, call_kwargs in mock_print.call_args_list if call_args)
        assert found_warning, f"Expected warning containing '{overwrite_core_message}' not found in calls: {mock_print.call_args_list}"
        found_path = any(str(output_file.resolve()) in call_args[0] for call_args, call_kwargs in mock_print.call_args_list if call_args)
        assert found_path, f"Expected path '{output_file.resolve()}' not found in warning calls: {mock_print.call_args_list}"


def test_construct_paths_quiet_flag(tmpdir, capsys):
    """
    Test that construct_paths prints input and output file paths when 'quiet' is False,
    and does not print when 'quiet' is True.
    """
    tmp_path = Path(str(tmpdir))

    # Create input files
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')
    code_file = tmp_path / 'my_project.py'
    code_file.write_text('print("Hello World")')
    error_file = tmp_path / 'errors.log'
    error_file.write_text('Error log')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'error_file': str(error_file),
    }
    force = True
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    # Test with quiet=False
    quiet = False
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

        # Use try-except to prevent test failure if construct_paths fails unexpectedly
        try:
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
        except Exception as e:
            pytest.fail(f"construct_paths failed unexpectedly with quiet=False: {e}")

        captured = capsys.readouterr()
        # Check for specific markers in the output
        assert "Input files:" in captured.out
        # Check for filename instead of resolved path to avoid line wrapping issues
        assert prompt_file.name in captured.out
        assert "Output files:" in captured.out
        assert mock_output_path.name in captured.out
        assert "Detected language:" in captured.out
        assert "Basename:" in captured.out

    # Test with quiet=True
    quiet = True
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

        try:
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
        except Exception as e:
            pytest.fail(f"construct_paths failed unexpectedly with quiet=True: {e}")

        captured = capsys.readouterr()
        # No informational output should be printed to stdout
        assert captured.out == ''
        # Error messages might go to stderr, check if needed
        assert captured.err == ''


def test_construct_paths_invalid_command(tmpdir):
    """
    Test that construct_paths raises a ValueError when an invalid command is provided
    (assuming generate_output_paths raises it).
    """
    tmp_path = Path(str(tmpdir))

    # Create input files
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'invalid_command'
    command_options = {}

    # Mock generate_output_paths to raise ValueError for the invalid command
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', side_effect=ValueError(f"Unknown command '{command}' provided.")):
        with pytest.raises(ValueError) as excinfo:
            construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
    assert f"Unknown command '{command}'" in str(excinfo.value)


def test_construct_paths_missing_command_options(tmpdir):
    """
    Test that construct_paths handles missing command options (None) gracefully.
    """
    tmp_path = Path(str(tmpdir))

    # Create input files
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = None  # Missing command options

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        try:
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
            # Check that defaults are used and no exception is raised
            assert input_strings['prompt_file'] == 'Prompt content'
            assert language == 'python'
            assert output_file_paths['output'] == str(mock_output_path)
        except Exception as e:
            pytest.fail(f"construct_paths failed with command_options=None: {e}")


def test_construct_paths_unsupported_extension_error(tmpdir):
    """
    Test that construct_paths raises ValueError when language cannot be determined.
    (Simulates unsupported extension leading to no language found).
    """
    tmp_path = Path(str(tmpdir))

    # Create input file with a generic name, no language suffix
    prompt_file = tmp_path / 'my_project.prompt'
    prompt_file.write_text('Prompt content')
    # Add a code file with an extension that get_language will return None for
    code_file_unsupported = tmp_path / 'my_code.unsupported'
    code_file_unsupported.write_text('...')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file_unsupported)
        }
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    # Mock get_language to return None for all inputs
    # Mock get_extension to return '' for unknown languages
    def dynamic_get_ext_unsupported(lang): return "" # Always return ""
    with patch('pdd.construct_paths.get_extension', side_effect=dynamic_get_ext_unsupported), \
         patch('pdd.construct_paths.get_language', return_value=None), \
         patch('pdd.construct_paths.generate_output_paths'): # Mock to prevent its errors
        with pytest.raises(ValueError) as excinfo:
            construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
        assert "Could not determine language" in str(excinfo.value)


def test_construct_paths_special_characters_in_filenames(tmpdir):
    """
    Test that construct_paths properly handles filenames with special characters.
    """
    tmp_path = Path(str(tmpdir))

    # Create input files with special characters
    # Use a name that includes a language suffix to ensure language detection works
    prompt_file_name = 'my_project @123!_python.prompt'
    prompt_file = tmp_path / prompt_file_name
    prompt_file.write_text('Prompt content')
    expected_basename = 'my_project @123!'

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output @ speciali.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    # Mocks should reflect the determined language/extension
    with patch('pdd.construct_paths.get_extension', return_value='.py') as mock_get_ext, \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:

        # Make get_extension dynamic for _strip_language_suffix
        def dynamic_get_extension(lang_candidate):
            if lang_candidate == 'python': return '.py'
            return ''
        mock_get_ext.side_effect = dynamic_get_extension

        mock_generate_output_paths.return_value = mock_output_paths_dict_str

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Check that the special characters are handled without errors
        assert input_strings['prompt_file'] == 'Prompt content'
        assert language == 'python'
        # Check basename extraction was correct
        mock_generate_output_paths.assert_called_once_with(
            command=command,
            output_locations={},
            basename=expected_basename, # Verify basename was extracted correctly
            language='python',
            file_extension='.py'
        )


def test_construct_paths_no_input_files(tmpdir):
    """
    Test that construct_paths raises a ValueError when no input files are provided.
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
    # Check the specific error message
    assert "No input files provided" == str(excinfo.value)


def test_construct_paths_conflicting_language_specification(tmpdir):
    """
    Test that command options language overrides filename language.
    """
    tmp_path = Path(str(tmpdir))

    # Language in filename is 'python'
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')

    input_file_paths = {'prompt_file': str(prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    # Language specified in command options is 'javascript'
    command_options = {'language': 'javascript'}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.js' # Expect .js output
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    # Mocks should reflect the *explicitly chosen* language (javascript)
    with patch('pdd.construct_paths.get_extension', return_value='.js'), \
         patch('pdd.construct_paths.get_language', return_value='javascript'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str) as mock_gen_paths:

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Command option should take precedence
        assert language == 'javascript'
        # Check that generate_output_paths was called with javascript details
        mock_gen_paths.assert_called_once_with(
            command=command,
            output_locations={}, # Filtered options should be empty here
            basename='my_project', # Basename from filename
            language='javascript', # Correct language passed
            file_extension='.js'   # Correct extension passed
        )
        assert output_file_paths['output'] == str(mock_output_path)


def test_construct_paths_missing_error_file_key(tmpdir):
    """
    Test that construct_paths handles input_file_paths without an 'error_file' key.
    """
    tmp_path = Path(str(tmpdir))

    # Create input files
    prompt_file = tmp_path / 'my_project_python.prompt'
    prompt_file.write_text('Prompt content')
    code_file = tmp_path / 'my_project.py'
    code_file.write_text('print("Hello World")')

    # error_file key not provided
    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
    }
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        try:
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
            # Check that construct_paths does not fail
            assert 'error_file' not in input_strings # error_file wasn't loaded
            assert language == 'python'
            assert output_file_paths['output'] == str(mock_output_path)
        except Exception as e:
            pytest.fail(f"construct_paths failed with missing 'error_file' key: {e}")


def test_construct_paths_nonexistent_directory_input(tmpdir):
    """
    Test that construct_paths raises FileNotFoundError early for non-existent input paths.
    """
    tmp_path = Path(str(tmpdir))

    # Create a path that does not exist
    nonexistent_dir = tmp_path / 'nonexistent'
    # Don't create the directory
    prompt_file_str = str(nonexistent_dir / 'my_project_python.prompt')

    input_file_paths = {'prompt_file': prompt_file_str}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    with pytest.raises(FileNotFoundError) as excinfo:
        # No mocks needed as error should happen during path resolution
        construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    # Check if the *missing directory* path string is in the FileNotFoundError message
    # because resolve(strict=True) fails on the first missing component.
    assert str(nonexistent_dir) in str(excinfo.value)


def test_construct_paths_relative_paths(tmpdir):
    """
    Test that construct_paths correctly handles relative file paths.
    """
    tmp_path = Path(str(tmpdir))

    # Change the working directory to tmpdir
    original_cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        # Create input files with relative paths from the new CWD
        prompt_file_rel_str = 'my_project_python.prompt'
        prompt_file_rel = Path(prompt_file_rel_str)
        prompt_file_rel.write_text('Prompt content')

        input_file_paths = {'prompt_file': prompt_file_rel_str} # Use relative string
        force = True
        quiet = True
        command = 'generate'
        command_options = {}

        # Mock generate_output_paths to return resolved Path objects as STRINGS
        # Output path should also be resolved relative to the new CWD (tmp_path)
        mock_output_path = tmp_path / 'output.py'
        mock_output_paths_dict_str = {'output': str(mock_output_path)}

        with patch('pdd.construct_paths.get_extension', return_value='.py'), \
             patch('pdd.construct_paths.get_language', return_value='python'), \
             patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
            # Check that files are correctly found and read
            assert input_strings['prompt_file'] == 'Prompt content'
            assert language == 'python'
            # Check output path is resolved correctly (should be absolute string)
            assert output_file_paths['output'] == str(mock_output_path.resolve())

    finally:
        # Change back to the original directory
        os.chdir(original_cwd)


def test_construct_paths_symbolic_links(tmpdir):
    """
    Test that construct_paths correctly resolves symbolic links in file paths.
    """
    tmp_path = Path(str(tmpdir))

    # Create actual file
    real_prompt_file = tmp_path / 'real_my_project_python.prompt' # Add lang suffix
    real_prompt_file.write_text('Prompt content')
    expected_basename = 'real_my_project'

    # Create a symbolic link (use Path.symlink_to)
    symlink_prompt_file = tmp_path / 'link_to_project.prompt' # Different name for link
    # Ensure the target exists before creating the link
    assert real_prompt_file.exists()
    try:
        symlink_prompt_file.symlink_to(real_prompt_file)
    except OSError:
        pytest.skip("Symbolic link creation failed (permissions or OS support?)") # Skip if symlink fails
    assert symlink_prompt_file.is_symlink()

    input_file_paths = {'prompt_file': str(symlink_prompt_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}

    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}

    # Mocks should reflect the *resolved* file's language
    with patch('pdd.construct_paths.get_extension', return_value='.py') as mock_get_ext, \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths:

        # Make get_extension dynamic for _strip_language_suffix
        def dynamic_get_extension(lang_candidate):
            if lang_candidate == 'python': return '.py'
            return ''
        mock_get_ext.side_effect = dynamic_get_extension

        mock_generate_output_paths.return_value = mock_output_paths_dict_str

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
        # Check that the symlink is correctly resolved and content read
        assert input_strings['prompt_file'] == 'Prompt content'
        # Language should be determined from the *resolved* file name
        assert language == 'python'
        # Check basename extraction used the resolved file
        mock_generate_output_paths.assert_called_once_with(
            command=command,
            output_locations={},
            basename=expected_basename, # Basename from the real file
            language='python',
            file_extension='.py'
        )

# --- Fixture and tests below seem to use tmp_path_factory correctly ---
# --- Need to adjust path comparisons to use absolute paths ---

@pytest.fixture(scope="module")
def setup_test_files(tmp_path_factory):
    """Fixture to set up test files for the tests."""
    test_dir = tmp_path_factory.mktemp("test_files")
    (test_dir / "unfinished_prompt_python.prompt").write_text("Test prompt content")
    (test_dir / "main_gen_prompt.prompt").write_text("Test prompt content")
    (test_dir / "unfinished_prompt.py").write_text("def test_function():\n    pass")
    # Add bash file for bash test
    (test_dir / "regression_bash.prompt").write_text("Bash prompt")
    # Create output dir for bash test
    (test_dir / "output").mkdir(exist_ok=True)
    return test_dir

def test_construct_paths_example_command(setup_test_files):
    """Test the 'example' command, expecting absolute output path."""
    input_file_paths = {
        "code_file": str(setup_test_files / "unfinished_prompt.py"),
        "prompt_file": str(setup_test_files / "unfinished_prompt_python.prompt")
    }
    command_options = {"output": None} # Let generate_output_paths create default

    # Mock generate_output_paths to return what it *should* return (absolute path string)
    expected_output_filename = "unfinished_prompt_example.py"
    # Assume output goes to CWD unless env var is set or --output used
    # For testing, let's assume CWD is where pytest runs
    expected_output_path = Path.cwd() / expected_output_filename
    mock_output_paths_dict_str = {'output': str(expected_output_path)}

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=True, quiet=True, command="example", command_options=command_options
        )

        assert language == "python"
        # Compare against the expected absolute path string
        assert output_file_paths["output"] == str(expected_output_path)

def test_construct_paths_generate_command(setup_test_files):
    """Test the 'generate' command with output dir, expecting absolute path."""
    input_file_paths = {
        "prompt_file": str(setup_test_files / "main_gen_prompt.prompt") # No language suffix
    }
    # Specify output directory relative to test files dir
    output_dir_rel = "gen_output"
    output_dir_abs = setup_test_files / output_dir_rel
    output_dir_abs.mkdir(exist_ok=True)
    command_options = {"output": str(output_dir_abs)} # Pass absolute path

    # Mock generate_output_paths to return the expected absolute path string inside the dir
    # The actual filename doesn't matter much here as we expect an error before generation
    expected_output_filename = "main_gen.prompt"
    expected_output_path = output_dir_abs / expected_output_filename
    mock_output_paths_dict_str = {'output': str(expected_output_path)}

    # Mock language detection helpers - expect language determination to fail
    # Mock get_extension to return '' for unknown languages
    def mock_get_extension_func_gen(lang):
        return ''
    # Mock get_language to return None (simulating failure to find lang)
    def mock_get_language_func_gen(ext_or_name):
        return None

    # Expect ValueError because language cannot be determined from 'main_gen_prompt.prompt'
    with pytest.raises(ValueError) as excinfo:
         with patch('pdd.construct_paths.get_extension', side_effect=mock_get_extension_func_gen), \
              patch('pdd.construct_paths.get_language', side_effect=mock_get_language_func_gen), \
              patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
              construct_paths(
                  input_file_paths=input_file_paths,
                  force=True, quiet=True, command="generate", command_options=command_options
              )
    assert "Could not determine language" in str(excinfo.value)


def test_construct_paths_bash_example(setup_test_files):
    """
    Test generate command for a bash script, expecting absolute path.
    Uses setup_test_files fixture.
    """
    # Define input file paths relative to the fixture directory
    prompt_file_path = setup_test_files / "regression_bash.prompt"
    input_file_paths = {"prompt_file": str(prompt_file_path)}

    # Define command options - output to a subdirectory within the fixture dir
    output_dir_rel = "output" # Relative to setup_test_files
    output_dir_abs = setup_test_files / output_dir_rel
    command_options = {"output": str(output_dir_abs)} # Pass absolute path

    # Expected output file path (absolute string)
    expected_output_file = output_dir_abs / "regression.sh"
    expected_output_file_paths_str = {"output": str(expected_output_file)}
    expected_language = "bash"

    # Mock generate_output_paths to return the expected absolute path string
    mock_output_paths_dict_str = {'output': str(expected_output_file)}

    # Mock language detection for _bash.prompt
    # Mock get_language to return 'bash' based on suffix logic (simulated)
    def mock_get_language_func_bash(ext_or_name):
        # This mock simulates the outcome of _determine_language step 3
        # It won't be called directly by step 3, but we mock the final result
        return 'bash'
    # Mock get_extension to return '.sh' for 'bash' language AND recognize 'bash' suffix
    def mock_get_extension_func_bash(lang_or_suffix):
        if lang_or_suffix == 'bash': return '.sh' # Used by generate_output_paths AND _determine_language suffix check
        return '' # Needed for suffix check in _determine_language

    # Patch get_extension with side effect, patch get_language with fixed return
    with patch('pdd.construct_paths.get_extension', side_effect=mock_get_extension_func_bash), \
         patch('pdd.construct_paths.get_language', return_value='bash'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

        # Call the construct_paths function
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=True, quiet=False, command="generate", command_options=command_options
        )

        # Assert that the output file paths match the expected absolute output string
        assert output_file_paths == expected_output_file_paths_str, (
            f"Expected output file paths: {expected_output_file_paths_str}, but got: {output_file_paths}"
        )
        assert language == expected_language, (
            f"Expected language: {expected_language}, but got: {language}"
        )
        assert "prompt_file" in input_strings
        assert input_strings["prompt_file"] == "Bash prompt"

        # Clean up: Remove the generated output file if it exists
        # Use the expected path for cleanup
        if expected_output_file.exists():
            os.remove(expected_output_file)

def test_construct_paths_change_command_language_detection(tmpdir):
    """
    Test that construct_paths correctly handles language detection for the change command
    when the prompt file doesn't include a language suffix.
    
    The change command should default to assuming the prompt is an LLM prompt
    even when the file doesn't have a language suffix in its name.
    """
    tmp_path = Path(str(tmpdir))
    
    # Create a test change prompt file without language suffix
    change_prompt_file = tmp_path / 'change.prompt'
    change_prompt_file.write_text('Change this prompt to include error handling')
    
    # Create a test input code file for the change command
    code_file = tmp_path / 'input_code.py'
    code_file.write_text('def example(): print("Hello")')
    
    # Create a test input prompt file
    input_prompt_file = tmp_path / 'input_prompt.prompt'
    input_prompt_file.write_text('Write a function that prints Hello')
    
    input_file_paths = {
        'change_prompt_file': str(change_prompt_file),
        'input_code': str(code_file),
        'input_prompt_file': str(input_prompt_file),
    }
    
    force = True
    quiet = True
    command = 'change'
    command_options = {}
    
    # Mock functions to isolate the test
    mock_output_path = tmp_path / 'modified_input_prompt.prompt'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}
    
    # After implementing the fix, language detection for the 'change' command
    # should now default to 'python' and not raise a ValueError
    with patch('pdd.construct_paths.get_extension', side_effect=lambda lang: '.py' if lang == 'python' else ''), \
         patch('pdd.construct_paths.get_language', side_effect=lambda ext: 'python' if ext == '.py' else ''), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        
        # This should now succeed with the default language being 'python'
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
        
        # The language should be properly set to python
        assert language == 'python'
        assert isinstance(output_file_paths['output'], str)
        assert output_file_paths['output'] == str(mock_output_path)
    
    # Also create a test case for a different command with no language indicators
    no_lang_prompt_file = tmp_path / 'generic.prompt'
    no_lang_prompt_file.write_text('Generic prompt with no language suffix')
    
    input_file_paths_no_lang = {
        'prompt_file': str(no_lang_prompt_file),
    }
    
    # Test with a different command without language indicators
    with patch('pdd.construct_paths.get_extension', side_effect=lambda lang: '.py' if lang == 'python' else ''), \
         patch('pdd.construct_paths.get_language', side_effect=lambda ext: 'python' if ext == '.py' else ''), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        
        # The "generate" command should raise ValueError with no language indicators
        with pytest.raises(ValueError) as excinfo:
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths_no_lang, force, quiet, "generate", command_options
            )
        
        # The error should be about not being able to determine language
        assert "Could not determine language" in str(excinfo.value)

def test_construct_paths_detect_command_language_detection(tmpdir):
    """
    Test that construct_paths correctly handles language detection for the detect command
    when the change_file doesn't include a language suffix.
    
    The detect command should default to assuming the language is 'prompt'
    even when the file doesn't have a language suffix in its name.
    """
    tmp_path = Path(str(tmpdir))
    
    # Create a test change file without language suffix
    change_file = tmp_path / 'update_description.prompt'
    change_file.write_text('Change description with no language suffix')
    
    # Create just one prompt file to keep the test simple
    prompt_file = tmp_path / 'prompt1.prompt'
    prompt_file.write_text('Some generic prompt content')
    
    # Input file paths for the detect command - we just need change_file for the test
    input_file_paths = {
        'change_file': str(change_file),
        'prompt_file': str(prompt_file)  # Use a simple key-value pair
    }
    
    force = True
    quiet = True
    command = 'detect'
    command_options = {}
    
    # Mock functions to isolate the test
    mock_output_path = tmp_path / 'detect_output.csv'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}
    
    # Test the special handling for detect command with change_file
    with patch('pdd.construct_paths.get_extension', side_effect=lambda lang: '.prompt' if lang == 'prompt' else '.py' if lang == 'python' else ''), \
         patch('pdd.construct_paths.get_language', side_effect=lambda ext: 'python' if ext == '.py' else ''), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        
        # This should succeed with the default language being 'prompt'
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
        
        # The language should be properly set to prompt
        assert language == 'prompt'
        assert isinstance(output_file_paths['output'], str)
        assert output_file_paths['output'] == str(mock_output_path)
    
    # Now test what happens if we use a different command
    # The 'detect' special case should not be triggered for other commands
    with patch('pdd.construct_paths.get_extension', side_effect=lambda lang: '.prompt' if lang == 'prompt' else '.py' if lang == 'python' else ''), \
         patch('pdd.construct_paths.get_language', side_effect=lambda ext: 'python' if ext == '.py' else ''), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
        
        # Using a different command should result in ValueError
        with pytest.raises(ValueError) as excinfo:
            input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, "generate", command_options  # Use different command
            )
        
        # The error would be about not being able to determine language
        assert "Could not determine language" in str(excinfo.value)

def test_construct_paths_bug_command_language_detection(tmpdir):
    """
    Test that construct_paths correctly handles None language values for the bug command.
    This specifically tests the fix for the scenario where language was set to None.
    """
    tmp_path = Path(str(tmpdir))

    # Create the input files exactly matching the failing command
    prompt_file = tmp_path / 'get_extension_python.prompt'
    prompt_file.write_text('Prompt content for bug test')

    code_file = tmp_path / 'get_extension.py'
    code_file.write_text('def get_extension(): pass')

    program_file = tmp_path / 'get_extension_example.py'
    program_file.write_text('import get_extension')

    current_output = tmp_path / 'current_output.txt'
    current_output.write_text('Current output')

    desired_output = tmp_path / 'desired_output.txt'
    desired_output.write_text('Desired output')

    input_file_paths = {
        'prompt_file': str(prompt_file),
        'code_file': str(code_file),
        'program_file': str(program_file),
        'current_output': str(current_output),
        'desired_output': str(desired_output)
    }

    force = True
    quiet = True
    command = 'bug'
    command_options = {
        'output': str(tmp_path / 'bug_test_get_extension.py'),
        'language': None  # Explicitly set to None to mimic the bug
    }

    # Mock generate_output_paths to return a dictionary of output paths
    output_test_path = tmp_path / 'bug_test_get_extension.py'
    mock_output_paths = {'output': str(output_test_path)}

    # Test Part 1: Mock _determine_language to return None - the fix should handle this gracefully
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths), \
         patch('pdd.construct_paths._determine_language', return_value=None):  # Simulate the bug where language is None

        # Now that the fix is in place, this should run without error
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Verify the fallback language was set correctly for 'bug' command
        assert language is not None, "Language should not be None"
        assert language.lower() == 'python', f"Language should default to 'python', got '{language}'"
        assert isinstance(language, str), "Language should be a string"

    # Test Part 2: Without mocking _determine_language, ensure standard behavior
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths):
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Verify correct behavior with regular language detection
        assert language is not None, "Language should not be None"
        assert language.lower() == 'python', f"Language should be 'python', got '{language}'"
        assert isinstance(language, str), "Language should be a string"