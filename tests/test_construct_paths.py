# test_construct_paths.py

import pytest
from pathlib import Path
from unittest import mock
from unittest.mock import patch, MagicMock, ANY
import sys
import os

# Mock generate_output_paths before importing construct_paths if it's needed globally
# Or mock within each test as currently done.

# Import after potentially modifying sys.path
from pdd.construct_paths import construct_paths, list_available_contexts

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

        _, input_strings, output_file_paths, language = construct_paths(
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

        _, input_strings, output_file_paths, language = construct_paths(
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
                 patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths, \
                 patch('pdd.construct_paths._find_pddrc_file', return_value=None):

                mock_generate_output_paths.return_value = mock_output_paths_dict_str
                try:
                    _, input_strings, output_file_paths, language = construct_paths(
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
                    file_extension=mock_ext, # Use the extension determined for mocking
                    context_config={}
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
        _, _, _, language1 = construct_paths(input_file_paths_1, True, True, 'generate', command_options_1)
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
        _, _, _, language2 = construct_paths(input_file_paths_2, True, True, 'generate', command_options_2)
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
        _, _, _, language3 = construct_paths(input_file_paths_3, True, True, 'generate', command_options_3)
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
         _, _, _, language5 = construct_paths(input_file_paths_5, True, True, 'generate', command_options_5)
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

        _, input_strings, output_file_paths, language = construct_paths(
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
            _, input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
        except Exception as e:
            pytest.fail(f"construct_paths failed unexpectedly with quiet=False: {e}")

        captured = capsys.readouterr()
        # Remove newlines from captured output to make assertions robust against line wrapping by rich
        captured_out_no_newlines = captured.out.replace('\n', '')

        # Check for specific markers in the output
        assert "Input files:" in captured_out_no_newlines
        # Check for filename instead of resolved path to avoid line wrapping issues
        assert prompt_file.name in captured_out_no_newlines
        assert "Output files:" in captured_out_no_newlines
        assert mock_output_path.name in captured_out_no_newlines
        assert "Detected language:" in captured_out_no_newlines
        assert "Basename:" in captured_out_no_newlines

    # Test with quiet=True
    quiet = True
    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):

        try:
            _, input_strings, output_file_paths, language = construct_paths(
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


# ---- Context listing tests (merged) ----

def test_list_available_contexts_no_pddrc(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    names = list_available_contexts()
    assert names == ["default"]


def test_list_available_contexts_with_pddrc(tmp_path, monkeypatch):
    pddrc = tmp_path / ".pddrc"
    pddrc.write_text(
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '  alt:\n'
        '    paths: ["src/**"]\n'
        '  dev:\n'
        '    paths: ["dev/**"]\n'
    )
    monkeypatch.chdir(tmp_path)
    names = list_available_contexts()
    assert set(names) == {"default", "alt", "dev"}


def test_list_available_contexts_malformed_pddrc(tmp_path, monkeypatch):
    (tmp_path / ".pddrc").write_text('version: "1.0"\n')  # Missing contexts root
    monkeypatch.chdir(tmp_path)
    with pytest.raises(ValueError):
        list_available_contexts()


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
            _, input_strings, output_file_paths, language = construct_paths(
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
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths, \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None):

        # Make get_extension dynamic for _strip_language_suffix
        def dynamic_get_extension(lang_candidate):
            if lang_candidate == 'python': return '.py'
            return ''
        mock_get_ext.side_effect = dynamic_get_extension

        mock_generate_output_paths.return_value = mock_output_paths_dict_str

        _, input_strings, output_file_paths, language = construct_paths(
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
            file_extension='.py',
            context_config={}
        )


def test_construct_paths_no_input_files(tmpdir):
    """
    Test that construct_paths raises a ValueError when no input files are provided
    for a command that requires them (i.e., not 'sync').
    """
    input_file_paths = {}
    force = True
    quiet = True
    command = 'generate' # Use a command other than sync
    command_options = {}

    with pytest.raises(ValueError) as excinfo:
        construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    # Check the specific error message
    assert "No input files provided" in str(excinfo.value)


def test_construct_paths_sync_discovery_mode(tmpdir):
    """
    Test that construct_paths runs in 'discovery mode' for the sync command
    when no input files are provided.
    """
    input_file_paths = {} # No inputs
    force = False
    quiet = True
    command = 'sync'
    command_options = {"basename": "my_sync_project"}
    
    # Mock generate_output_paths which is used internally for path inference
    mock_output_paths = {
        "generate_output_path": str(tmpdir / "src" / "my_sync_project.py"),
        "test_output_path": str(tmpdir / "tests" / "test_my_sync_project.py"),
        "example_output_path": str(tmpdir / "examples" / "ex_my_sync_project.py"),
    }
    
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths) as mock_gen_paths:
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

    # Assert that discovery mode was successful
    assert "prompts_dir" in resolved_config
    assert "code_dir" in resolved_config
    assert "tests_dir" in resolved_config
    assert "examples_dir" in resolved_config
    
    # Check that paths are derived correctly
    assert Path(resolved_config["prompts_dir"]).name == "prompts"
    assert Path(resolved_config["code_dir"]).name == "src"
    assert Path(resolved_config["tests_dir"]).name == "tests"
    assert Path(resolved_config["examples_dir"]).name == "examples"
    
    # Assert that other return values are empty/default
    assert input_strings == {}
    assert output_file_paths == {}
    assert language == ""


def test_construct_paths_sync_discovery_requires_basename(tmpdir):
    """
    In sync discovery mode (no inputs), a 'basename' in command_options is required.
    The function should raise a ValueError if it is missing.
    """
    input_file_paths = {}
    force = False
    quiet = True
    command = 'sync'
    command_options = {}  # No basename provided

    with pytest.raises(ValueError) as excinfo:
        construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

    assert 'Basename must be provided' in str(excinfo.value)


def test_construct_paths_sync_discovery_prompts_dir_bug_fix(tmpdir):
    """
    Test that the sync discovery mode correctly calculates prompts_dir path
    for both default context and configured context scenarios.
    
    This is a regression test for the original bug where prompts_dir was 
    calculated incorrectly, and ensures the new context-aware logic works correctly.
    """
    input_file_paths = {}  # No inputs for sync discovery mode
    force = False
    quiet = True
    command = 'sync'
    
    # Test 1: Default context scenario (no .pddrc context config)
    # This simulates the original user's scenario: /tmp/sync_test with pi.py
    command_options = {"basename": "pi"}
    working_dir = Path("/tmp/sync_test")
    generate_output_path = working_dir / "pi.py"
    
    mock_output_paths_default = {
        "generate_output_path": str(generate_output_path),
        "test_output_path": str(working_dir / "test_pi.py"),
        "example_output_path": str(working_dir / "pi_example.py"),
    }
    
    # Mock no context config (default behavior) - also mock context detection
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_default), \
         patch('pdd.construct_paths._get_context_config', return_value={}):
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    
    # For default context: prompts should be sibling to generated code
    expected_prompts_dir = working_dir / "prompts"
    actual_prompts_dir = Path(resolved_config["prompts_dir"])
    
    assert actual_prompts_dir == expected_prompts_dir, \
        f"Default context: prompts_dir should be {expected_prompts_dir}, but got {actual_prompts_dir}"
    
    assert Path(resolved_config["code_dir"]) == working_dir, \
        f"Default context: code_dir should be {working_dir}"

    # Test 2: Configured context scenario (with .pddrc context config)
    # This simulates PDD project scenario with generate_output_path: "pdd/"
    command_options_context = {"basename": "simple_math"}
    working_dir_context = Path("/path/to/project")
    generate_output_path_context = working_dir_context / "pdd" / "simple_math.py"
    
    mock_output_paths_context = {
        "generate_output_path": str(generate_output_path_context),
        "test_output_path": str(working_dir_context / "tests" / "test_simple_math.py"),
        "example_output_path": str(working_dir_context / "examples" / "simple_math_example.py"),
    }
    
    # Mock context config with output path configuration
    mock_context_config = {"generate_output_path": "pdd/"}
    
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_context), \
         patch('pdd.construct_paths._get_context_config', return_value=mock_context_config):
        
        resolved_config_context, _, _, _ = construct_paths(
            input_file_paths, force, quiet, command, command_options_context
        )
    
    # For configured context: prompts should be at root level (sibling to pdd/)
    expected_prompts_dir_context = "prompts"  # Relative path at root level
    actual_prompts_dir_context = resolved_config_context["prompts_dir"]
    
    assert actual_prompts_dir_context == expected_prompts_dir_context, \
        f"Configured context: prompts_dir should be '{expected_prompts_dir_context}', but got '{actual_prompts_dir_context}'"
    
    assert Path(resolved_config_context["code_dir"]) == working_dir_context / "pdd", \
        f"Configured context: code_dir should be {working_dir_context / 'pdd'}"


def test_construct_paths_sync_discovery_context_detection(tmpdir):
    """
    Test that sync discovery mode correctly detects and handles different context configurations.
    This ensures the context_config detection logic works properly.
    """
    input_file_paths = {}
    force = False
    quiet = True
    command = 'sync'
    command_options = {"basename": "test"}
    
    # Test case 1: Empty context config (should use default logic)
    mock_output_paths = {
        "generate_output_path": "/some/path/test.py",
        "test_output_path": "/some/path/test_test.py",
        "example_output_path": "/some/path/test_example.py",
    }
    
    empty_context = {}
    
    # Mock all context detection to ensure no .pddrc is found

    # Also mock Path.cwd() to return a directory with no prompt files to test default logic
    mock_cwd = Path("/test/empty/directory")
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths), \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None), \
         patch('pdd.construct_paths._get_context_config', return_value=empty_context), \
         patch('pdd.construct_paths.Path.cwd', return_value=mock_cwd):

        
        resolved_config, _, _, _ = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    
    # With no .pddrc and empty context, should use default logic (relative to generated code)
    assert resolved_config["prompts_dir"] == "/some/path/prompts"
    
    # Test case 2: Context with output_path config (should use context-aware logic)
    context_with_output_path = {
        "generate_output_path": "src/",
        "test_output_path": "tests/",
        "some_other_config": "value"
    }
    
    # Mock finding .pddrc and getting context config with output paths
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths), \
         patch('pdd.construct_paths._find_pddrc_file', return_value=Path('/fake/.pddrc')), \
         patch('pdd.construct_paths._load_pddrc_config', return_value={'contexts': {'test': context_with_output_path}}), \
         patch('pdd.construct_paths._detect_context', return_value='test'), \
         patch('pdd.construct_paths._get_context_config', return_value=context_with_output_path), \
         patch('pdd.construct_paths.Path.cwd', return_value=mock_cwd):

        
        resolved_config_context, _, _, _ = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    
    # With context config containing output paths, should use context-aware logic
    assert resolved_config_context["prompts_dir"] == "prompts"
    
    # Test case 3: Context with non-output config (should use default logic)
    context_without_output_path = {
        "strength": 0.8,
        "temperature": 0.1,
        "some_setting": "value"
    }
    
    # Mock finding .pddrc but context config has no output paths
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths), \
         patch('pdd.construct_paths._find_pddrc_file', return_value=Path('/fake/.pddrc')), \
         patch('pdd.construct_paths._load_pddrc_config', return_value={'contexts': {'test': context_without_output_path}}), \
         patch('pdd.construct_paths._detect_context', return_value='test'), \
         patch('pdd.construct_paths._get_context_config', return_value=context_without_output_path), \
         patch('pdd.construct_paths.Path.cwd', return_value=mock_cwd):

        
        resolved_config_no_output, _, _, _ = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    
    # Without output path config, should use default logic
    assert resolved_config_no_output["prompts_dir"] == "/some/path/prompts"


def test_construct_paths_sync_discovery_current_directory(tmpdir):
    """
    Test that sync discovery mode checks current working directory first for prompt files.
    """
    tmp_path = Path(str(tmpdir))
    
    # Create a prompt file in the "current working directory" (test directory)
    prompt_file = tmp_path / 'calculator_python.prompt'
    prompt_file.write_text('Create a calculator function')
    
    input_file_paths = {}
    force = False
    quiet = True
    command = 'sync'
    command_options = {"basename": "calculator"}
    
    mock_output_paths = {
        "generate_output_path": "/some/other/path/calculator.py",
        "test_output_path": "/some/other/path/test_calculator.py",
        "example_output_path": "/some/other/path/calculator_example.py",
    }
    
    # Mock Path.cwd() to return our test directory and glob to find the prompt file
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths), \
         patch('pdd.construct_paths.Path.cwd', return_value=tmp_path), \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None), \
         patch('pdd.construct_paths._get_context_config', return_value={}):
        
        resolved_config, _, _, _ = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    
    # Should use current working directory since prompt file was found there
    assert resolved_config["prompts_dir"] == str(tmp_path)
    assert resolved_config["code_dir"] == str(tmp_path)

def test_construct_paths_sync_discovery_honors_pddrc_generate_output_path_override(tmpdir):
    """
    When generate_output_paths returns a default-root code path, construct_paths (sync discovery)
    should still honor .pddrc context generate_output_path (e.g., 'pdd/') and place code under it.
    """
    input_file_paths = {}
    force = False
    quiet = True
    command = 'sync'
    command_options = {"basename": "simple_math"}

    # .pddrc context config indicating code should go under 'pdd/'
    context_cfg = {
        "generate_output_path": "pdd/",
        "test_output_path": "tests/",
        "example_output_path": "examples/",
    }

    # Fix current working directory for absolute resolution
    mock_cwd = Path("/project")

    # Simulate generator returning a CWD-root location for code (problematic case)
    # Establish mock CWD for this test
    mock_cwd = Path("/project")
    mocked_gen_paths = {
        "generate_output_path": str(mock_cwd / "simple_math.py"),
        "test_output_path": str(mock_cwd / "tests" / "test_simple_math.py"),
        "example_output_path": str(mock_cwd / "examples" / "simple_math_example.py"),
    }

    with patch('pdd.construct_paths.generate_output_paths', return_value=mocked_gen_paths), \
         patch('pdd.construct_paths._find_pddrc_file', return_value=Path('/fake/.pddrc')), \
         patch('pdd.construct_paths._load_pddrc_config', return_value={'contexts': {'regression': {'defaults': context_cfg}}}), \
         patch('pdd.construct_paths._detect_context', return_value='regression'), \
         patch('pdd.construct_paths._get_context_config', return_value=context_cfg), \
         patch('pdd.construct_paths.Path.cwd', return_value=mock_cwd):

        resolved_config, _, _, _ = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

    # Code dir should reflect the .pddrc setting (under /project/pdd), not /root
    assert resolved_config["code_dir"] == str(mock_cwd / "pdd")
    # Prompts directory should be root-level (sibling to pdd/)
    assert resolved_config["prompts_dir"] == "prompts"

def test_construct_paths_sync_with_prompt_honors_pddrc_generate_output_path_override(tmpdir):
    """
    In normal sync (with prompt_file given), ensure generate_output_path is overridden
    to .pddrc's generate_output_path even if generator returns a default root path.
    """
    tmp_path = Path(str(tmpdir))
    # Create a prompt file so language/basename resolve normally
    prompt_file = tmp_path / 'simple_math_python.prompt'
    prompt_file.write_text('Make simple math module')

    input_file_paths = {"prompt_file": str(prompt_file)}
    force = True
    quiet = True
    command = 'sync'
    command_options = {"basename": "simple_math", "language": "python"}

    # Establish mock CWD for this test
    mock_cwd = Path("/project")
    mocked_gen_paths = {
        "generate_output_path": str(mock_cwd / "simple_math.py"),
        "test_output_path": str(mock_cwd / "tests" / "test_simple_math.py"),
        "example_output_path": str(mock_cwd / "examples" / "simple_math_example.py"),
    }

    context_cfg = {
        "generate_output_path": "pdd/",
        "test_output_path": "tests/",
        "example_output_path": "examples/",
    }

    # mock_cwd defined above

    with patch('pdd.construct_paths.generate_output_paths', return_value=mocked_gen_paths), \
         patch('pdd.construct_paths._find_pddrc_file', return_value=Path('/fake/.pddrc')), \
         patch('pdd.construct_paths._load_pddrc_config', return_value={'contexts': {'regression': {'defaults': context_cfg}}}), \
         patch('pdd.construct_paths._detect_context', return_value='regression'), \
         patch('pdd.construct_paths._get_context_config', return_value=context_cfg), \
         patch('pdd.construct_paths.Path.cwd', return_value=mock_cwd):

        resolved_config, _, output_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

    # Output path should have been overridden to /project/pdd/simple_math.py
    assert Path(output_paths["generate_output_path"]).parent == mock_cwd / "pdd"
    assert resolved_config["code_dir"] == str(mock_cwd / "pdd")

def test_construct_paths_sync_discovery_fallback_to_context_logic(tmpdir):
    """
    Test that sync discovery mode falls back to context-aware logic when no prompts in CWD.
    """
    tmp_path = Path(str(tmpdir))
    
    # Don't create any prompt files in the test directory
    
    input_file_paths = {}
    force = False
    quiet = True
    command = 'sync'
    command_options = {"basename": "calculator"}
    
    mock_output_paths = {
        "generate_output_path": "/some/path/calculator.py",
        "test_output_path": "/some/path/test_calculator.py",
        "example_output_path": "/some/path/calculator_example.py",
    }
    
    # Mock Path.cwd() to return our test directory (with no prompt files)
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths), \
         patch('pdd.construct_paths.Path.cwd', return_value=tmp_path), \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None), \
         patch('pdd.construct_paths._get_context_config', return_value={}):
        
        resolved_config, _, _, _ = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )
    
    # Should fall back to default logic since no prompt files found in CWD
    assert resolved_config["prompts_dir"] == "/some/path/prompts"


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
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str) as mock_gen_paths, \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None):

        _, input_strings, output_file_paths, language = construct_paths(
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
            file_extension='.js',   # Correct extension passed
            context_config={}
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
            _, input_strings, output_file_paths, language = construct_paths(
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
            _, input_strings, output_file_paths, language = construct_paths(
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
         patch('pdd.construct_paths.generate_output_paths') as mock_generate_output_paths, \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None):

        # Make get_extension dynamic for _strip_language_suffix
        def dynamic_get_extension(lang_candidate):
            if lang_candidate == 'python': return '.py'
            return ''
        mock_get_ext.side_effect = dynamic_get_extension

        mock_generate_output_paths.return_value = mock_output_paths_dict_str

        _, input_strings, output_file_paths, language = construct_paths(
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
            file_extension='.py',
            context_config={}
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

        _, input_strings, output_file_paths, language = construct_paths(
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
        if lang == "prompt":
            return ".prompt" # As per language_format.csv
        return ''
    # Mock get_language to return None (simulating failure to find lang initially, suffix logic takes over)
    def mock_get_language_func_gen(ext_or_name):
        return None # Ensures suffix logic in _determine_language is reached

    # Expect ValueError because language cannot be determined from 'main_gen_prompt.prompt'
    # UPDATE: With _is_known_language, "prompt" will be determined.
    # with pytest.raises(ValueError) as excinfo:
    with patch('pdd.construct_paths._is_known_language', side_effect=lambda x: True if x == "prompt" else False) as mock_is_known, \
         patch('pdd.construct_paths.get_extension', side_effect=mock_get_extension_func_gen) as mock_get_ext, \
         patch('pdd.construct_paths.get_language', side_effect=mock_get_language_func_gen) as mock_get_lang, \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str) as mock_gen_ops, \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None):
        # Correctly unpack the return tuple from construct_paths
        _, actual_input_strings, actual_output_file_paths, actual_determined_language = construct_paths(
            input_file_paths=input_file_paths,
            force=True, quiet=True, command="generate", command_options=command_options
        )
    # assert "Could not determine language" in str(excinfo.value)
    assert actual_determined_language == "prompt"
    # Basename should be "main_gen" after stripping "_prompt"
    mock_gen_ops.assert_called_once_with(
        command='generate',
        output_locations=command_options, # output_dir_abs is in command_options['output']
        basename='main_gen',
        language='prompt',
        file_extension='.prompt',
        context_config={}
    )


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
        _, input_strings, output_file_paths, language = construct_paths(
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
        _, input_strings, output_file_paths, language = construct_paths(
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
            _, input_strings, output_file_paths, language = construct_paths(
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
        _, input_strings, output_file_paths, language = construct_paths(
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
            _, input_strings, output_file_paths, language = construct_paths(
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
        _, input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Verify the fallback language was set correctly for 'bug' command
        assert language is not None, "Language should not be None"
        assert language.lower() == 'python', f"Language should default to 'python', got '{language}'"
        assert isinstance(language, str), "Language should be a string"

    # Test Part 2: Without mocking _determine_language, ensure standard behavior
    with patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths):
        _, input_strings, output_file_paths, language = construct_paths(
            input_file_paths, force, quiet, command, command_options
        )

        # Verify correct behavior with regular language detection
        assert language is not None, "Language should not be None"
        assert language.lower() == 'python', f"Language should be 'python', got '{language}'"
        assert isinstance(language, str), "Language should be a string"

def test_construct_paths_force_overwrite(tmpdir):
    """
    Test that construct_paths does NOT prompt for overwrite when force=True,
    even if output files exist.
    """
    tmp_path = Path(str(tmpdir))

    # Create dummy input file
    prompt_file = tmp_path / 'project_python.prompt'
    prompt_file.write_text('prompt')

    # Create dummy EXISTING output file
    output_file = tmp_path / 'project_verified.py'
    output_file.write_text('existing code')

    input_file_paths = {'prompt_file': str(prompt_file)}
    # Simulate options for a command like 'verify' that uses 'output_code'
    command_options = {'output_code': str(output_file)}
    command = 'verify' # Use a command that generates output_code
    force = True
    quiet = False # Set quiet to False to ensure prompt would normally appear

    # Mock generate_output_paths to return the existing output path
    mock_output_paths_dict = {'output_code': str(output_file)}

    # Mock click.confirm to ensure it's NOT called
    with patch('pdd.construct_paths.click.confirm', side_effect=Exception("Should not be called")) as mock_confirm, \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.get_extension', return_value='.py'): # Add mock for get_extension

        try:
            # Call the function with force=True
            _, input_strings, output_file_paths, language = construct_paths(
                input_file_paths=input_file_paths,
                force=force,
                quiet=quiet,
                command=command,
                command_options=command_options
            )
            # Assertions after the call (optional, main check is no exception/call to confirm)
            assert 'prompt_file' in input_strings
            assert output_file_paths['output_code'] == str(output_file)
            assert language == 'python'

        except SystemExit:
            pytest.fail("construct_paths exited unexpectedly, likely due to unmocked confirmation prompt.")
        except Exception as e:
             # Let other unexpected exceptions fail the test naturally
             # but specifically check if it was the mocked confirm exception
             if "Should not be called" in str(e):
                  pytest.fail("click.confirm was called unexpectedly despite force=True")
             else:
                  raise # Re-raise other exceptions

    # Primary assertion: click.confirm should NOT have been called
    mock_confirm.assert_not_called()

def test_construct_paths_verify_command_default_and_options(tmpdir):
    """
    Test construct_paths for the 'verify' command, checking default path generation
    (via mocked generate_output_paths) and user-supplied command_options for output_program.
    """
    tmp_path = Path(str(tmpdir))
    quiet = True
    force = True

    # Create dummy input files required by 'verify'
    prompt_file = tmp_path / "verify_prompt_python.prompt"
    prompt_file.write_text("Verify this prompt")
    code_file = tmp_path / "verify_code.py"
    code_file.write_text("print('hello')")
    program_file = tmp_path / "run_verify.py" # The executable program
    program_file.write_text("#!/usr/bin/env python\nprint('program output')")

    input_file_paths = {
        "prompt_file": str(prompt_file),
        "code_file": str(code_file),
        "program_file": str(program_file), # Actual executable
        "verification_program": str(program_file) # program_file is also used as verification_program for verify
    }

    # --- Scenario 1: Default paths via mocked generate_output_paths ---
    command_options_default = {}
    
    mock_gen_paths_return_default = {
        "output_results": str(tmp_path / "default_verify_results.log"),
        "output_code": str(tmp_path / "default_verified_code.py"),
        "output_program": str(tmp_path / "default_verified_program.py")
    }

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_gen_paths_return_default) as mock_gen_paths_default:
        
        _, input_strings, output_paths_default, _ = construct_paths(
            input_file_paths, force, quiet, "verify", command_options_default
        )
        
        mock_gen_paths_default.assert_called_once()
        assert output_paths_default == mock_gen_paths_return_default

    # --- Scenario 2: User specifies output_program in command_options ---
    user_output_program_path = str(tmp_path / "user_specified_program_verified.exe")
    command_options_user_program = {
        "output_program": user_output_program_path
        # output_results and output_code will be determined by generate_output_paths
    }

    # generate_output_paths will be called with output_program already specified.
    # It should respect it and generate defaults for others.
    mock_gen_paths_return_user_program = {
        "output_results": str(tmp_path / "default_verify_results_for_user_prog.log"),
        "output_code": str(tmp_path / "default_verified_code_for_user_prog.py"),
        "output_program": user_output_program_path # This should match the input
    }

    with patch('pdd.construct_paths.get_extension', return_value='.py'), \
         patch('pdd.construct_paths.get_language', return_value='python'), \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_gen_paths_return_user_program) as mock_gen_paths_user:
        
        _, input_strings, output_paths_user, _ = construct_paths(
            input_file_paths, force, quiet, "verify", command_options_user_program
        )

        # Check that generate_output_paths was called with output_program in its command_options
        # The actual call to generate_output_paths inside construct_paths will have its
        # output_locations (from command_options) passed as a keyword argument.
        _args, called_kwargs = mock_gen_paths_user.call_args
        
        # Ensure 'output_locations' was passed as a keyword argument
        assert "output_locations" in called_kwargs
        # Check the content of the 'output_locations' dictionary
        assert called_kwargs['output_locations'].get("output_program") == user_output_program_path
        
        assert output_paths_user == mock_gen_paths_return_user_program
        assert output_paths_user["output_program"] == user_output_program_path

def test_construct_paths_handles_makefile_suffix_correctly_or_fails_if_buggy(tmpdir):
    """
    Tests that language determination for 'makefile' from a prompt suffix
    works correctly if the underlying CSV/logic is fixed.
    If the current bug (where get_extension('makefile') yields an empty string
    leading to ValueError) is present, this test will fail due to an unhandled exception.
    """
    tmp_path = Path(str(tmpdir))
    prompt_file = tmp_path / "MyProject_makefile.prompt"
    prompt_file.write_text("Test prompt for Makefile")

    input_file_paths = {"prompt_file": str(prompt_file)}
    command = "generate"
    command_options = {} # No explicit language

    # Dummy output path for mocking generate_output_paths
    mock_output_path_str = str(tmp_path / "MyProject.out") # Could be .mk if that's the fix
    mock_output_paths_dict_str = {"output": mock_output_path_str}

    # Mock get_language to return None, ensuring that the logic proceeds to
    # parse the language from the prompt file's suffix.
    # Mock generate_output_paths as its internal logic is not under test here.
    # We DO NOT mock get_extension for "makefile", allowing the actual (buggy or fixed)
    # logic to run.
    with patch('pdd.construct_paths.get_language', return_value=None) as mock_get_lang, \
         patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str) as mock_gen_ops, \
         patch('pdd.construct_paths._find_pddrc_file', return_value=None):

        # If the bug (ValueError in _determine_language for "makefile") is present,
        # this call will raise an unhandled ValueError, and the test will FAIL.
        # If the bug is fixed, this call will succeed.
        _, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=True,
            quiet=True,
            command=command,
            command_options=command_options
        )

        # These assertions are only reached if construct_paths does NOT raise an error.
        assert language == "makefile", \
            "If the 'makefile' language bug is fixed, determined_language should be 'makefile'."

        # This assertion verifies that generate_output_paths is called with the correct
        # parameters, assuming a fix where 'makefile' is recognized and its extension
        # might be '.mk' (or empty if the logic changes to support that).
        # For this test, we'll assume the fix involves get_extension("makefile") returning ".mk".
        # The basename should be "MyProject" after stripping "_makefile".
        mock_gen_ops.assert_called_once_with(
            command='generate',
            output_locations={},
            basename='MyProject',
            language='makefile',
            file_extension='',  # Makefiles have no extension
            context_config={}
        )


# Test context detection functions that were in test_context_detection.py
def test_find_pddrc_file_real():
    """Test _find_pddrc_file finds the actual .pddrc file in the project."""
    from pdd.construct_paths import _find_pddrc_file
    
    pddrc_path = _find_pddrc_file()
    assert pddrc_path is not None, "Should find .pddrc file in project"
    assert Path(pddrc_path).exists(), "Found .pddrc path should exist"
    assert Path(pddrc_path).name == ".pddrc", "Should find file named .pddrc"


def test_detect_context_real():
    """Test _detect_context with actual .pddrc configuration."""
    from pdd.construct_paths import _find_pddrc_file, _load_pddrc_config, _detect_context
    
    pddrc_path = _find_pddrc_file()
    if pddrc_path:
        config = _load_pddrc_config(pddrc_path)
        current_dir = Path.cwd()
        
        context = _detect_context(current_dir, config)
        assert context is not None, "Should detect a context"
        assert isinstance(context, str), "Context should be a string"


def test_get_context_config_real():
    """Test _get_context_config with actual .pddrc configuration."""
    from pdd.construct_paths import _find_pddrc_file, _load_pddrc_config, _detect_context, _get_context_config
    
    pddrc_path = _find_pddrc_file()
    if pddrc_path:
        config = _load_pddrc_config(pddrc_path)
        current_dir = Path.cwd()
        context = _detect_context(current_dir, config)
        
        if context:
            context_config = _get_context_config(config, context)
            assert isinstance(context_config, dict), "Context config should be a dictionary"
            # Check for expected keys based on the .pddrc format
            if 'generate_output_path' in context_config:
                assert isinstance(context_config['generate_output_path'], str)
            if 'example_output_path' in context_config:
                assert isinstance(context_config['example_output_path'], str)


def test_language_detection_without_pdd_path_fallback(tmpdir):
    """
    Test that language detection works without PDD_PATH environment variable using CSV fallback.
    This tests the fix for Issue #88 where language detection failed when PDD_PATH was not set.
    """
    tmp_path = Path(str(tmpdir))
    
    # Create a test Python file
    test_file = tmp_path / 'test_function.py'
    test_file.write_text('def hello():\n    return "hello"\n')
    
    input_file_paths = {'code_file': str(test_file)}
    force = True
    quiet = True
    command = 'generate'
    command_options = {}
    
    # Mock generate_output_paths to return resolved Path objects as STRINGS
    mock_output_path = tmp_path / 'output.py'
    mock_output_paths_dict_str = {'output': str(mock_output_path)}
    
    # Test with PDD_PATH unset (simulating the original bug)
    original_pdd_path = os.environ.pop('PDD_PATH', None)
    
    try:
        # Mock get_language to raise ValueError (simulating missing PDD_PATH)
        with patch('pdd.construct_paths.get_language', side_effect=ValueError("PDD_PATH environment variable is not set")), \
             patch('pdd.construct_paths.generate_output_paths', return_value=mock_output_paths_dict_str):
            
            # This should now succeed with CSV fallback instead of failing
            _, input_strings, output_file_paths, language = construct_paths(
                input_file_paths, force, quiet, command, command_options
            )
            
            # Verify language detection worked via CSV fallback
            assert language == 'python', f"Expected 'python', got '{language}'"
            assert input_strings['code_file'] == 'def hello():\n    return "hello"\n'
            assert output_file_paths['output'] == str(mock_output_path)
            
    finally:
        # Restore original PDD_PATH
        if original_pdd_path:
            os.environ['PDD_PATH'] = original_pdd_path
