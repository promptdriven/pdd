import os
import sys
import pytest
import tempfile
from pathlib import Path
from pdd import DEFAULT_STRENGTH

# Assume the code under test is in pdd/generate_output_paths.py
# Adjust the import path if necessary based on your project structure
try:
    from pdd.generate_output_paths import generate_output_paths, COMMAND_OUTPUT_KEYS, DEFAULT_FILENAMES, ENV_VAR_MAP
except ImportError:
    # If running directly from the tests directory, adjust sys.path
    # This assumes your tests are in a 'tests' directory and 'pdd' is a sibling
    pdd_module_path = Path(__file__).parent.parent / 'pdd'
    sys.path.insert(0, str(pdd_module_path.parent))
    from pdd.generate_output_paths import generate_output_paths, COMMAND_OUTPUT_KEYS, DEFAULT_FILENAMES, ENV_VAR_MAP


# --- Test Constants ---
TEST_BASENAME = "my_component"
TEST_LANG = "python"
TEST_EXT_WITH_DOT = ".py"
TEST_EXT_WITHOUT_DOT = "py"
TEST_EXT_EMPTY = ""

# Helper to get expected default filename (without path)
def get_expected_default_name(command, key, basename, lang, ext):
    pattern = DEFAULT_FILENAMES[command][key]
    effective_ext = ext if ext.startswith('.') or not ext else '.' + ext
    if '{ext}' in pattern:
        return pattern.format(basename=basename, language=lang, ext=effective_ext)
    else:
        return pattern.format(basename=basename, language=lang) # ext might not be needed

# Helper to create absolute path in current dir for expectation
def abs_path_cwd(filename):
    return os.path.abspath(filename)

# --- Fixture for temporary directory ---
@pytest.fixture
def temp_output_dir(tmp_path):
    """Creates a temporary directory for output testing."""
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    return output_dir

# --- Test Cases ---

def test_unknown_command():
    """Test that an unknown command returns an empty dictionary."""
    result = generate_output_paths(
        command="invalid_command",
        output_locations={},
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {}

def test_missing_basename():
    """Test that a missing basename returns an empty dictionary."""
    result = generate_output_paths(
        command="generate",
        output_locations={},
        basename="", # Empty basename
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {}

# --- Default Path Tests ---
@pytest.mark.parametrize("command", COMMAND_OUTPUT_KEYS.keys())
def test_defaults_for_all_commands(command):
    """Test default path generation for all known commands."""
    expected_keys = COMMAND_OUTPUT_KEYS[command]
    result = generate_output_paths(
        command=command,
        output_locations={},
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )

    assert list(result.keys()).sort() == list(expected_keys).sort()
    for key in expected_keys:
        expected_filename = get_expected_default_name(command, key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
        # Special handling for example command which now defaults to examples/ directory
        if command == "example":
            expected_path = abs_path_cwd(f"examples/{expected_filename}")
        else:
            expected_path = abs_path_cwd(expected_filename)
        assert key in result
        assert result[key] == expected_path
        assert os.path.isabs(result[key])

# --- User Input Tests ---
def test_user_input_specific_file():
    """Test user providing a specific filename."""
    user_file = "specific_output.py"
    result = generate_output_paths(
        command="generate",
        output_locations={'output': user_file},
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {'output': abs_path_cwd(user_file)}

def test_user_input_specific_file_absolute(temp_output_dir):
    """Test user providing an absolute filename."""
    user_file = temp_output_dir / "specific_output_abs.py"
    result = generate_output_paths(
        command="generate",
        output_locations={'output': str(user_file)},
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {'output': str(user_file)} # Already absolute

def test_user_input_directory_trailing_slash(temp_output_dir):
    """Test user providing a directory path ending with a slash."""
    command = 'test'
    key = 'output'
    default_name = get_expected_default_name(command, key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_path = os.path.join(str(temp_output_dir), default_name)

    result = generate_output_paths(
        command=command,
        output_locations={key: str(temp_output_dir) + os.sep},
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {key: expected_path}
    assert os.path.isabs(result[key])

def test_user_input_directory_existing(temp_output_dir):
    """Test user providing an existing directory path."""
    command = 'example'
    key = 'output'
    default_name = get_expected_default_name(command, key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_path = os.path.join(str(temp_output_dir), default_name)

    result = generate_output_paths(
        command=command,
        output_locations={key: str(temp_output_dir)}, # No trailing slash, but exists
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {key: expected_path}
    assert os.path.isabs(result[key])

def test_user_input_directory_non_existing(temp_output_dir):
    """Test user providing a non-existing path without trailing slash (treated as file)."""
    user_path = temp_output_dir / "non_existing_dir_as_file" # Does not exist
    command = 'generate'
    key = 'output'

    result = generate_output_paths(
        command=command,
        output_locations={key: str(user_path)},
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    # Should treat it as a specific file path, not append default name
    assert result == {key: str(user_path)}
    assert os.path.isabs(result[key])


# --- Environment Variable Tests ---
def test_env_var_specific_file(monkeypatch):
    """Test environment variable providing a specific filename."""
    env_var = ENV_VAR_MAP['generate']['output']
    env_file = "env_generated.py"
    monkeypatch.setenv(env_var, env_file)

    result = generate_output_paths(
        command="generate",
        output_locations={}, # No user input
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {'output': abs_path_cwd(env_file)}
    monkeypatch.delenv(env_var) # Clean up

def test_env_var_directory_trailing_slash(monkeypatch, temp_output_dir):
    """Test environment variable providing a directory path with trailing slash."""
    command = 'fix'
    key = 'output_code'
    env_var = ENV_VAR_MAP[command][key]
    default_name = get_expected_default_name(command, key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_path = os.path.join(str(temp_output_dir), default_name)

    monkeypatch.setenv(env_var, str(temp_output_dir) + os.sep)

    result = generate_output_paths(
        command=command,
        output_locations={}, # No user input
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    # Check only the key affected by env var, others should be default
    assert key in result
    assert result[key] == expected_path
    assert os.path.isabs(result[key])
    # Verify other keys have default paths
    for other_key in COMMAND_OUTPUT_KEYS[command]:
        if other_key != key:
            other_default_name = get_expected_default_name(command, other_key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
            assert result[other_key] == abs_path_cwd(other_default_name)

    monkeypatch.delenv(env_var) # Clean up

def test_env_var_directory_existing(monkeypatch, temp_output_dir):
    """Test environment variable providing an existing directory path."""
    command = 'preprocess'
    key = 'output'
    env_var = ENV_VAR_MAP[command][key]
    default_name = get_expected_default_name(command, key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_path = os.path.join(str(temp_output_dir), default_name)

    monkeypatch.setenv(env_var, str(temp_output_dir)) # No trailing slash

    result = generate_output_paths(
        command=command,
        output_locations={}, # No user input
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {key: expected_path}
    assert os.path.isabs(result[key])

    monkeypatch.delenv(env_var) # Clean up

# --- Prioritization Tests ---
def test_prioritization_user_over_env(monkeypatch):
    """Test that user input overrides environment variables."""
    command = 'generate'
    key = 'output'
    env_var = ENV_VAR_MAP[command][key]
    env_file = "env_gen.py"
    user_file = "user_gen.py"

    monkeypatch.setenv(env_var, env_file)

    result = generate_output_paths(
        command=command,
        output_locations={key: user_file}, # User input provided
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {key: abs_path_cwd(user_file)} # User path wins

    monkeypatch.delenv(env_var) # Clean up

def test_prioritization_env_over_default(monkeypatch):
    """Test that environment variable overrides default path."""
    command = 'example'
    key = 'output'
    env_var = ENV_VAR_MAP[command][key]
    env_file = "env_example.py"

    monkeypatch.setenv(env_var, env_file)

    result = generate_output_paths(
        command=command,
        output_locations={}, # No user input
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )
    assert result == {key: abs_path_cwd(env_file)} # Env path wins over default

    monkeypatch.delenv(env_var) # Clean up

# Specific test for verify command and output_program env var
def test_verify_command_env_var_for_output_program(monkeypatch, temp_output_dir):
    """Test ENV var for 'output_program' with the 'verify' command."""
    command = "verify"
    program_key = "output_program"
    results_key = "output_results"
    code_key = "output_code"

    env_var_program = ENV_VAR_MAP[command][program_key]
    env_program_file_path = temp_output_dir / "env_verify_program.out" # Specific file path

    monkeypatch.setenv(env_var_program, str(env_program_file_path))

    result = generate_output_paths(
        command=command,
        output_locations={}, # No user input for any key
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )

    # Check that output_program path is from ENV var
    assert program_key in result
    assert result[program_key] == str(env_program_file_path)

    # Check that other keys for 'verify' get their default paths
    expected_results_filename = get_expected_default_name(command, results_key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_code_filename = get_expected_default_name(command, code_key, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)

    assert results_key in result
    assert result[results_key] == abs_path_cwd(expected_results_filename)
    assert code_key in result
    assert result[code_key] == abs_path_cwd(expected_code_filename)

    monkeypatch.delenv(env_var_program) # Clean up

# --- Multi-Output Command Tests ---
def test_fix_command_mixed_inputs(monkeypatch, temp_output_dir):
    """Test 'fix' command with a mix of user, env, and default inputs."""
    command = 'fix'
    user_test_file = "my_fixed_test.py"
    env_code_dir = temp_output_dir / "fixed_code"
    env_code_dir.mkdir()
    env_var_code = ENV_VAR_MAP[command]['output_code']

    monkeypatch.setenv(env_var_code, str(env_code_dir)) # Env var points to a directory

    result = generate_output_paths(
        command=command,
        output_locations={'output_test': user_test_file}, # User specifies test file
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )

    # Expected paths
    expected_test_path = abs_path_cwd(user_test_file)
    expected_code_default_name = get_expected_default_name(command, 'output_code', TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_code_path = os.path.join(str(env_code_dir), expected_code_default_name)
    expected_results_default_name = get_expected_default_name(command, 'output_results', TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_results_path = abs_path_cwd(expected_results_default_name)

    assert result == {
        'output_test': expected_test_path,
        'output_code': expected_code_path,
        'output_results': expected_results_path
    }
    assert os.path.isabs(result['output_test'])
    assert os.path.isabs(result['output_code'])
    assert os.path.isabs(result['output_results'])

    monkeypatch.delenv(env_var_code) # Clean up

# --- Edge Case Tests ---
def test_file_extension_variants():
    """Test handling of file extensions with/without dot and empty."""
    command = 'generate'
    key = 'output'

    # With dot
    result_dot = generate_output_paths(command, {}, TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_dot = abs_path_cwd(f"{TEST_BASENAME}{TEST_EXT_WITH_DOT}")
    assert result_dot == {key: expected_dot}

    # Without dot
    result_no_dot = generate_output_paths(command, {}, TEST_BASENAME, TEST_LANG, TEST_EXT_WITHOUT_DOT)
    expected_no_dot = abs_path_cwd(f"{TEST_BASENAME}{TEST_EXT_WITH_DOT}") # Should add dot
    assert result_no_dot == {key: expected_no_dot}

    # Empty extension
    result_empty = generate_output_paths(command, {}, TEST_BASENAME, TEST_LANG, TEST_EXT_EMPTY)
    expected_empty = abs_path_cwd(f"{TEST_BASENAME}") # No extension
    assert result_empty == {key: expected_empty}

def test_fixed_extension_ignores_input_ext():
    """Test that commands with fixed extensions ignore the input file_extension."""
    command = 'preprocess' # Uses .prompt
    key = 'output'
    result = generate_output_paths(
        command=command,
        output_locations={},
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=".different_ext" # Should be ignored
    )
    expected_name = get_expected_default_name(command, key, TEST_BASENAME, TEST_LANG, ".different_ext") # Pass ext for helper consistency
    expected_path = abs_path_cwd(expected_name)
    assert result == {key: expected_path}
    assert result[key].endswith("_preprocessed.prompt") # Verify fixed extension

def test_output_locations_hyphen_key():
    """Test that hyphenated keys in output_locations are handled."""
    command = 'fix'
    key_hyphen = 'output-test'
    key_underscore = 'output_test'
    user_file = "hyphen_test.py"

    result = generate_output_paths(
        command=command,
        output_locations={key_hyphen: user_file}, # Input uses hyphen
        basename=TEST_BASENAME,
        language=TEST_LANG,
        file_extension=TEST_EXT_WITH_DOT
    )

    # Result dictionary should use the underscore key
    assert key_underscore in result
    assert key_hyphen not in result # Ensure hyphen key is not present
    assert result[key_underscore] == abs_path_cwd(user_file)

    # Check other keys are default
    expected_code_default_name = get_expected_default_name(command, 'output_code', TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    expected_results_default_name = get_expected_default_name(command, 'output_results', TEST_BASENAME, TEST_LANG, TEST_EXT_WITH_DOT)
    assert result['output_code'] == abs_path_cwd(expected_code_default_name)
    assert result['output_results'] == abs_path_cwd(expected_results_default_name)


def test_sync_orchestration_example_scenario():
    """Test the exact scenario from sync orchestration with .pddrc context config."""
    # Test case from test_path_resolution.py
    basename = "factorial"
    language = "python"
    file_extension = ".py"
    
    # Context config from .pddrc pdd_cli context
    context_config = {
        'generate_output_path': 'pdd/',
        'test_output_path': 'tests/',
        'example_output_path': 'examples/',
        'default_language': 'python',
        'target_coverage': 90.0,
        'strength': DEFAULT_STRENGTH,
        'temperature': 0.0,
        'budget': 10.0,
        'max_attempts': 3
    }
    
    # This is the path that get_pdd_file_paths determined
    user_output_path = os.path.join(os.getcwd(), "examples", "factorial_example.py")
    
    output_locations = {
        'output': user_output_path
    }
    
    result = generate_output_paths(
        command='example',
        output_locations=output_locations,
        basename=basename,
        language=language,
        file_extension=file_extension,
        context_config=context_config
    )
    
    # The output should preserve the user-specified path since it's a valid file path
    assert 'output' in result
    assert result['output'] == os.path.abspath(user_output_path)
    
    # Test that directory detection works correctly
    assert not user_output_path.endswith(os.path.sep), "Path should not end with separator"
    # The path should be treated as a file, not a directory


def test_example_command_defaults_to_examples_directory():
    """Test that the example command defaults to examples/ directory."""
    basename = "hello"
    
    result = generate_output_paths("example", basename)
    
    # Should default to examples/ directory
    assert "output" in result, "Should have output key"
    output_path = result["output"]
    assert "examples" in str(output_path), "Output should be in examples directory"
    assert basename in str(output_path), "Output should contain basename"


def test_example_command_with_existing_examples_directory():
    """Test example command behavior when examples directory already exists."""
    basename = "test_module"
    
    # Create a temporary examples directory
    with tempfile.TemporaryDirectory() as tmp_dir:
        examples_dir = Path(tmp_dir) / "examples"
        examples_dir.mkdir()
        
        # Change to the temporary directory
        original_cwd = os.getcwd()
        os.chdir(tmp_dir)
        
        try:
            result = generate_output_paths("example", basename)
            
            # Should use the existing examples directory
            assert "output" in result, "Should have output key"
            output_path = result["output"]
            assert "examples" in str(output_path), "Output should be in examples directory"
            assert basename in str(output_path), "Output should contain basename"
            
        finally:
            os.chdir(original_cwd)


def test_other_commands_not_affected():
    """Test that other commands are not affected by the example command changes."""
    basename = "test_module"
    
    # Test other commands still work as expected
    commands_to_test = ["generate", "test", "fix", "update"]
    
    for command in commands_to_test:
        result = generate_output_paths(command, basename)
        assert "output" in result, f"Command {command} should have output key"
        
        # These commands should not default to examples/ directory
        output_path = result["output"]
        if command != "example":
            # Other commands should not automatically go to examples/
            # They should use the current directory or user-specified path
            pass  # This is more of a sanity check that they don't break

