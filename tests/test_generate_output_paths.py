import os
import sys
import pytest
from pathlib import Path
from pdd import DEFAULT_STRENGTH

# Assume the code under test is in pdd/generate_output_paths.py
# Adjust the import path if necessary based on your project structure
try:
    from pdd.generate_output_paths import generate_output_paths, COMMAND_OUTPUT_KEYS, DEFAULT_FILENAMES, ENV_VAR_MAP, _get_default_filename
except ImportError:
    # If running directly from the tests directory, adjust sys.path
    # This assumes your tests are in a 'tests' directory and 'pdd' is a sibling
    pdd_module_path = Path(__file__).parent.parent / 'pdd'
    sys.path.insert(0, str(pdd_module_path.parent))
    from pdd.generate_output_paths import generate_output_paths, COMMAND_OUTPUT_KEYS, DEFAULT_FILENAMES, ENV_VAR_MAP, _get_default_filename


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
        # Default for 'example' now uses examples/ directory
        if command == 'example':
            expected_path = abs_path_cwd(os.path.join('examples', expected_filename))
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


# =============================================================================
# Issue #169 Regression Tests: Path Resolution Mode
# =============================================================================
#
# These tests verify the fix for GitHub Issue #169: Path resolution regression
# where running `pdd sync` from a subdirectory incorrectly resolved output paths
# relative to .pddrc location instead of CWD.
#
# Bug: Commit 3c8b2371 introduced config_base_dir that changed path resolution
# to always prioritize the .pddrc parent directory. This is correct for `fix`
# but breaks `sync`.
#
# Solution: Added `path_resolution_mode` parameter:
#   - "cwd" - resolves relative paths to current working directory (for sync)
#   - "config_base" - resolves relative paths to .pddrc location (for fix, etc.)
# =============================================================================

from unittest.mock import patch, MagicMock


class TestIssue169PathResolution:
    """Tests for Issue #169: Path resolution regression in sync from subdirectory."""

    @pytest.fixture
    def project_structure(self, tmp_path):
        """
        Create a project structure that mimics the bug scenario:

        project_root/           <- .pddrc here with generate_output_path: "src/"
        └── examples/hello/     <- CWD here when running sync
            └── hello.prompt
        """
        project_root = tmp_path / "project_root"
        project_root.mkdir()

        # Create .pddrc at project root
        pddrc = project_root / ".pddrc"
        pddrc.write_text("""
contexts:
  default:
    defaults:
      generate_output_path: src/
      test_output_path: tests/
      example_output_path: examples/
""")

        # Create subdirectory
        subdir = project_root / "examples" / "hello"
        subdir.mkdir(parents=True)

        # Create prompt file in subdirectory
        prompt_file = subdir / "hello_python.prompt"
        prompt_file.write_text("Write a hello world function")

        return {
            "project_root": project_root,
            "subdir": subdir,
            "pddrc": pddrc,
            "prompt_file": prompt_file,
        }

    def test_sync_from_subdirectory_resolves_paths_relative_to_cwd(
        self, project_structure
    ):
        """
        REGRESSION TEST for issue #169.

        When running sync from a subdirectory with path_resolution_mode="cwd":
        - CWD = project_root/examples/hello/
        - .pddrc at project_root with generate_output_path: "src/"
        - Result: CWD/src/hello.py (resolved from CWD, not .pddrc location)
        """
        project_root = project_structure["project_root"]
        subdir = project_structure["subdir"]

        # Context config from .pddrc
        context_config = {
            "generate_output_path": "src/",
            "test_output_path": "tests/",
            "example_output_path": "examples/",
        }

        # Save current CWD and change to subdir
        original_cwd = os.getcwd()
        try:
            os.chdir(subdir)

            # Call generate_output_paths with path_resolution_mode="cwd"
            # (as construct_paths now calls it for sync)
            result = generate_output_paths(
                command="sync",
                output_locations={},
                basename="hello",
                language="python",
                file_extension=".py",
                context_config=context_config,
                config_base_dir=str(project_root),  # .pddrc parent directory
                path_resolution_mode="cwd",  # Sync uses CWD-relative paths
            )

            # For sync command, the key is 'generate_output_path'
            generate_path = result.get("generate_output_path", "")

            # With the fix, paths should resolve relative to CWD (subdir)
            expected = str(subdir / "src" / "hello.py")
            assert generate_path == expected, \
                f"Expected {expected}, got {generate_path}"

        finally:
            os.chdir(original_cwd)

    def test_fix_command_should_use_config_base_to_avoid_path_doubling(
        self, project_structure
    ):
        """
        Verifies the original bug that commit 3c8b2371 fixed.

        Scenario:
        - .pddrc at project root with generate_output_path: "backend/functions/src/"
        - Running fix on backend/functions/prompts/calculator.prompt
        - Without config_base_dir: path doubles to backend/functions/prompts/backend/functions/src/
        - With config_base_dir: correctly resolves to backend/functions/src/
        """
        project_root = project_structure["project_root"]

        # Simulate the scenario from commit 3c8b2371
        context_config = {
            "generate_output_path": "backend/functions/src/",
            "test_output_path": "backend/functions/tests/",
        }

        # The input file is in a subdirectory
        input_file_dir = str(project_root / "backend" / "functions" / "prompts")

        # With config_base_dir (the fix from 3c8b2371):
        # Relative paths should resolve from project root, not input file dir
        # For fix command, the output keys are 'output_code', 'output_test', 'output_results'
        result = generate_output_paths(
            command="fix",
            output_locations={},
            basename="calculator",
            language="python",
            file_extension=".py",
            context_config=context_config,
            input_file_dir=input_file_dir,
            config_base_dir=str(project_root),
        )

        # For fix command, 'output_code' maps to 'generate_output_path' in context config
        generate_path = result.get("output_code", "")

        # Should NOT have path doubling
        assert "prompts/backend" not in generate_path, \
            f"Path doubling bug: got {generate_path}"

        # Should correctly resolve to project_root/backend/functions/src/
        # Note: fix command uses _fixed suffix in filename
        expected_path = str(project_root / "backend" / "functions" / "src" / "calculator_fixed.py")
        assert generate_path == expected_path, \
            f"Expected {expected_path}, got {generate_path}"

    def test_absolute_paths_not_affected_by_resolution_mode(self, project_structure):
        """
        Absolute paths in .pddrc should not be affected by resolution mode.
        """
        project_root = project_structure["project_root"]

        absolute_path = "/absolute/path/to/output/"
        context_config = {
            "generate_output_path": absolute_path,
            "test_output_path": "/absolute/tests/",
            "example_output_path": "/absolute/examples/",
        }

        result = generate_output_paths(
            command="sync",
            output_locations={},
            basename="test",
            language="python",
            file_extension=".py",
            context_config=context_config,
            config_base_dir=str(project_root),
        )

        generate_path = result.get("generate_output_path", "")

        # Absolute path should be used as-is
        assert generate_path.startswith("/absolute/path/to/output/"), \
            f"Absolute path should be preserved, got {generate_path}"

    def test_cli_output_override_takes_priority_for_generate(self, project_structure):
        """
        CLI --output should take priority over .pddrc configuration.
        This is priority level 1 in the resolution chain.
        """
        project_root = project_structure["project_root"]

        context_config = {
            "generate_output_path": "src/",
        }

        # CLI --output is passed via output_locations with key 'output' for generate command
        cli_output = str(project_root / "custom_output" / "myfile.py")
        output_locations = {
            "output": cli_output,
        }

        result = generate_output_paths(
            command="generate",
            output_locations=output_locations,
            basename="test",
            language="python",
            file_extension=".py",
            context_config=context_config,
            config_base_dir=str(project_root),
        )

        # For generate command, the key is 'output'
        generate_path = result.get("output", "")

        # CLI output should take priority
        assert generate_path == cli_output, \
            f"CLI --output should take priority, expected {cli_output}, got {generate_path}"

    def test_sync_from_project_root_same_as_config_base(self, project_structure):
        """
        When CWD equals .pddrc location, both resolution modes should produce same result.
        """
        project_root = project_structure["project_root"]

        context_config = {
            "generate_output_path": "src/",
            "test_output_path": "tests/",
            "example_output_path": "examples/",
        }

        # When running from project root, CWD == config_base_dir
        # Both modes should give the same result
        result = generate_output_paths(
            command="sync",
            output_locations={},
            basename="hello",
            language="python",
            file_extension=".py",
            context_config=context_config,
            config_base_dir=str(project_root),
        )

        generate_path = result.get("generate_output_path", "")

        # Should resolve to project_root/src/hello.py
        expected = str(project_root / "src" / "hello.py")
        assert generate_path == expected, \
            f"Expected {expected}, got {generate_path}"


class TestIssue169EnvVarPathResolution:
    """Tests for environment variable path resolution (Issue #169 related)."""

    def test_env_var_relative_path_resolution(self, tmp_path):
        """
        Environment variable relative paths should follow the same resolution
        logic as .pddrc paths.
        """
        project_root = tmp_path / "project"
        project_root.mkdir()

        # Set environment variable with relative path
        # For sync command, use PDD_GENERATE_OUTPUT_PATH
        with patch.dict(os.environ, {"PDD_GENERATE_OUTPUT_PATH": "env_output/"}):
            result = generate_output_paths(
                command="sync",
                output_locations={},
                basename="test",
                language="python",
                file_extension=".py",
                context_config={},  # No .pddrc config, will use env var
                config_base_dir=str(project_root),
            )

        generate_path = result.get("generate_output_path", "")

        # Env var relative path should be resolved using config_base_dir
        assert str(project_root / "env_output") in generate_path, \
            f"Env var path should resolve relative to config_base, got {generate_path}"

    def test_env_var_absolute_path_not_affected(self, tmp_path):
        """
        Absolute paths in environment variables should not be modified.
        """
        absolute_env_path = "/absolute/env/path/"

        with patch.dict(os.environ, {"PDD_GENERATE_OUTPUT_PATH": absolute_env_path}):
            result = generate_output_paths(
                command="sync",
                output_locations={},
                basename="test",
                language="python",
                file_extension=".py",
                context_config={},
                config_base_dir=str(tmp_path),
            )

        generate_path = result.get("generate_output_path", "")

        # Absolute env path should be preserved
        assert generate_path.startswith("/absolute/env/path/"), \
            f"Absolute env path should be preserved, got {generate_path}"


class TestIssue169PriorityChain:
    """
    Tests verifying the priority chain is maintained (Issue #169 related):
    1. CLI --output (highest)
    2. .pddrc context
    3. Environment variables
    4. Built-in defaults (lowest)
    """

    def test_cli_overrides_pddrc_for_generate(self, tmp_path):
        """CLI --output should override .pddrc configuration for generate command."""
        cli_path = str(tmp_path / "cli_output.py")

        result = generate_output_paths(
            command="generate",
            output_locations={"output": cli_path},
            basename="test",
            language="python",
            file_extension=".py",
            context_config={"generate_output_path": "pddrc_path/"},
            config_base_dir=str(tmp_path),
        )

        # For generate command, the key is 'output'
        assert result.get("output") == cli_path

    def test_pddrc_overrides_env_var_for_sync(self, tmp_path):
        """
        .pddrc configuration should override environment variables for sync.
        """
        with patch.dict(os.environ, {"PDD_GENERATE_OUTPUT_PATH": "env_path/"}):
            result = generate_output_paths(
                command="sync",
                output_locations={},
                basename="test",
                language="python",
                file_extension=".py",
                context_config={"generate_output_path": "pddrc_path/"},
                config_base_dir=str(tmp_path),
            )

        generate_path = result.get("generate_output_path", "")

        # Should use .pddrc path, not env var
        assert "pddrc_path" in generate_path, \
            f".pddrc should override env var, got {generate_path}"
        assert "env_path" not in generate_path

    def test_env_var_used_when_no_pddrc_config_for_sync(self, tmp_path):
        """
        Environment variable should be used when no .pddrc configuration exists for sync.
        """
        with patch.dict(os.environ, {"PDD_GENERATE_OUTPUT_PATH": "env_output/"}):
            result = generate_output_paths(
                command="sync",
                output_locations={},
                basename="test",
                language="python",
                file_extension=".py",
                context_config={},  # No .pddrc config
                config_base_dir=str(tmp_path),
            )

        generate_path = result.get("generate_output_path", "")

        # Should use env var path
        assert "env_output" in generate_path, \
            f"Should use env var when no .pddrc config, got {generate_path}"

    def test_default_used_when_no_config_or_env_for_sync(self, tmp_path, monkeypatch):
        """
        Built-in defaults should be used when no config or env var exists for sync.
        """
        # Ensure env var is not set
        monkeypatch.delenv("PDD_GENERATE_OUTPUT_PATH", raising=False)

        result = generate_output_paths(
            command="sync",
            output_locations={},
            basename="test",
            language="python",
            file_extension=".py",
            context_config={},
            config_base_dir=None,
        )

        generate_path = result.get("generate_output_path", "")

        # Should use default naming (basename.ext in current directory)
        assert "test.py" in generate_path, \
            f"Should use default naming, got {generate_path}"


class TestPathResolutionModeParameter:
    """
    Tests for the path_resolution_mode parameter (Issue #169).
    """

    def test_cwd_mode_resolves_relative_to_cwd(self, tmp_path):
        """
        When path_resolution_mode="cwd", relative paths should resolve relative to CWD.
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        subdir = project_root / "subdir"
        subdir.mkdir()

        context_config = {
            "generate_output_path": "src/",
            "test_output_path": "tests/",
            "example_output_path": "examples/",
        }

        # Save current CWD and change to subdir
        original_cwd = os.getcwd()
        try:
            os.chdir(subdir)

            result = generate_output_paths(
                command="sync",
                output_locations={},
                basename="hello",
                language="python",
                file_extension=".py",
                context_config=context_config,
                config_base_dir=str(project_root),
                path_resolution_mode="cwd",
            )

            generate_path = result.get("generate_output_path", "")

            # With path_resolution_mode="cwd", paths resolve relative to CWD (subdir)
            expected = str(subdir / "src" / "hello.py")
            assert generate_path == expected, \
                f"Expected {expected}, got {generate_path}"

        finally:
            os.chdir(original_cwd)

    def test_config_base_mode_resolves_relative_to_config_dir(self, tmp_path):
        """
        When path_resolution_mode="config_base" (default), relative paths resolve to config_base_dir.
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        subdir = project_root / "subdir"
        subdir.mkdir()

        context_config = {
            "generate_output_path": "src/",
        }

        # Save current CWD and change to subdir
        original_cwd = os.getcwd()
        try:
            os.chdir(subdir)

            result = generate_output_paths(
                command="fix",
                output_locations={},
                basename="hello",
                language="python",
                file_extension=".py",
                context_config=context_config,
                config_base_dir=str(project_root),
                path_resolution_mode="config_base",  # Explicit default
            )

            generate_path = result.get("output_code", "")

            # With path_resolution_mode="config_base", paths resolve relative to project_root
            expected = str(project_root / "src" / "hello_fixed.py")
            assert generate_path == expected, \
                f"Expected {expected}, got {generate_path}"

        finally:
            os.chdir(original_cwd)

    def test_default_mode_is_config_base(self, tmp_path):
        """
        When path_resolution_mode is not specified, it defaults to "config_base".
        """
        project_root = tmp_path / "project"
        project_root.mkdir()
        subdir = project_root / "subdir"
        subdir.mkdir()

        context_config = {
            "generate_output_path": "src/",
        }

        # Save current CWD and change to subdir
        original_cwd = os.getcwd()
        try:
            os.chdir(subdir)

            # Don't pass path_resolution_mode - should use default "config_base"
            result = generate_output_paths(
                command="fix",
                output_locations={},
                basename="hello",
                language="python",
                file_extension=".py",
                context_config=context_config,
                config_base_dir=str(project_root),
            )

            generate_path = result.get("output_code", "")

            # Default should resolve relative to project_root (config_base behavior)
            expected = str(project_root / "src" / "hello_fixed.py")
            assert generate_path == expected, \
                f"Expected {expected}, got {generate_path}"

        finally:
            os.chdir(original_cwd)


# =============================================================================
# Subdirectory Basename Support Tests
# =============================================================================
#
# These tests verify support for subdirectory basenames like 'core/cloud'.
# When a basename contains a forward slash, the directory structure should be
# preserved in the output path, with filename patterns applied only to the
# final component (the actual name, not the directory part).
#
# Example: basename="core/cloud" with pattern="test_{basename}{ext}"
# - WRONG: test_core/cloud.py (forward slash interpreted as path separator in pattern)
# - RIGHT: core/test_cloud.py (directory preserved, pattern applied to name only)
# =============================================================================


class TestSubdirectoryBasenameSupport:
    """Tests for subdirectory basename support (e.g., 'core/cloud')."""

    def test_get_default_filename_with_subdirectory_basename(self):
        """Should preserve directory structure in output paths.

        _get_default_filename splits basename, applies pattern to name part,
        and prepends directory part.
        """
        # Test code generation: {basename}{ext} -> core/cloud.py
        result = _get_default_filename("sync", "generate_output_path", "core/cloud", "python", ".py")
        assert result == "core/cloud.py", f"Expected 'core/cloud.py', got '{result}'"

        # Test test generation: test_{basename}{ext} -> core/test_cloud.py (NOT test_core/cloud.py)
        result = _get_default_filename("sync", "test_output_path", "core/cloud", "python", ".py")
        assert result == "core/test_cloud.py", f"Expected 'core/test_cloud.py', got '{result}'"

        # Test example generation: {basename}_example{ext} -> core/cloud_example.py
        result = _get_default_filename("sync", "example_output_path", "core/cloud", "python", ".py")
        assert result == "core/cloud_example.py", f"Expected 'core/cloud_example.py', got '{result}'"

    def test_get_default_filename_deeply_nested_subdirectory(self):
        """Should handle deeply nested subdirectory basenames."""
        # Test deeply nested: commands/cli/generate -> commands/cli/test_generate.py
        result = _get_default_filename("sync", "test_output_path", "commands/cli/generate", "python", ".py")
        assert result == "commands/cli/test_generate.py", f"Expected 'commands/cli/test_generate.py', got '{result}'"

    def test_get_default_filename_flat_basename_unchanged(self):
        """Flat basenames (no slash) should work exactly as before."""
        # Existing behavior should be preserved
        result = _get_default_filename("sync", "generate_output_path", "calculator", "python", ".py")
        assert result == "calculator.py", f"Expected 'calculator.py', got '{result}'"

        result = _get_default_filename("sync", "test_output_path", "calculator", "python", ".py")
        assert result == "test_calculator.py", f"Expected 'test_calculator.py', got '{result}'"

    def test_generate_output_paths_with_subdirectory_basename(self, tmp_path):
        """Full integration test: generate_output_paths should handle subdirectory basenames."""
        project_root = tmp_path / "project"
        project_root.mkdir()

        context_config = {
            "generate_output_path": "pdd/",
            "test_output_path": "tests/",
            "example_output_path": "examples/",
        }

        result = generate_output_paths(
            command="sync",
            output_locations={},
            basename="core/cloud",
            language="python",
            file_extension=".py",
            context_config=context_config,
            config_base_dir=str(project_root),
        )

        # All paths should preserve subdirectory structure
        generate_path = result.get("generate_output_path", "")
        test_path = result.get("test_output_path", "")
        example_path = result.get("example_output_path", "")

        # Expected: pdd/core/cloud.py, tests/core/test_cloud.py, examples/core/cloud_example.py
        expected_generate = str(project_root / "pdd" / "core" / "cloud.py")
        expected_test = str(project_root / "tests" / "core" / "test_cloud.py")
        expected_example = str(project_root / "examples" / "core" / "cloud_example.py")

        assert generate_path == expected_generate, \
            f"Expected {expected_generate}, got {generate_path}"
        assert test_path == expected_test, \
            f"Expected {expected_test}, got {test_path}"
        assert example_path == expected_example, \
            f"Expected {expected_example}, got {example_path}"

    def test_fix_command_with_subdirectory_basename(self):
        """Fix command patterns should also support subdirectory basenames."""
        # test_{basename}_fixed{ext} -> core/test_cloud_fixed.py (NOT test_core/cloud_fixed.py)
        result = _get_default_filename("fix", "output_test", "core/cloud", "python", ".py")
        assert result == "core/test_cloud_fixed.py", f"Expected 'core/test_cloud_fixed.py', got '{result}'"

        # {basename}_fixed{ext} -> core/cloud_fixed.py
        result = _get_default_filename("fix", "output_code", "core/cloud", "python", ".py")
        assert result == "core/cloud_fixed.py", f"Expected 'core/cloud_fixed.py', got '{result}'"

