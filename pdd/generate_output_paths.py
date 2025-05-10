import os
import logging
from typing import Dict, List, Optional

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# --- Configuration Data ---

# Define the expected output keys for each command
# Use underscores for keys as requested
COMMAND_OUTPUT_KEYS: Dict[str, List[str]] = {
    'generate': ['output'],
    'example': ['output'],
    'test': ['output'],
    'preprocess': ['output'],
    'fix': ['output_test', 'output_code', 'output_results'],
    'split': ['output_sub', 'output_modified'],
    'change': ['output'],
    'update': ['output'],
    'detect': ['output'],
    'conflicts': ['output'],
    'crash': ['output', 'output_program'],
    'trace': ['output'],
    'bug': ['output'],
    'auto-deps': ['output'],
    'verify': ['output_results', 'output_code', 'output_program'],
}

# Define default filename patterns for each output key
# Placeholders: {basename}, {language}, {ext}
# Note: Patterns include the extension directly where it's fixed (e.g., .prompt, .log, .csv)
#       or use {ext} where it depends on the language.
DEFAULT_FILENAMES: Dict[str, Dict[str, str]] = {
    'generate': {'output': '{basename}{ext}'},
    'example': {'output': '{basename}_example{ext}'},
    'test': {'output': 'test_{basename}{ext}'},
    'preprocess': {'output': '{basename}_{language}_preprocessed.prompt'},
    'fix': {
        'output_test': 'test_{basename}_fixed{ext}',
        'output_code': '{basename}_fixed{ext}',
        'output_results': '{basename}_fix_results.log',
    },
    'split': {
        'output_sub': 'sub_{basename}.prompt',
        'output_modified': 'modified_{basename}.prompt',
    },
    'change': {'output': 'modified_{basename}.prompt'},
    'update': {'output': 'modified_{basename}.prompt'}, # Consistent with change/split default
    'detect': {'output': '{basename}_detect.csv'}, # Using basename as change_file_basename isn't available here
    'conflicts': {'output': '{basename}_conflict.csv'}, # Using basename as prompt1/2 basenames aren't available
    'crash': {
        'output': '{basename}_fixed{ext}',
        # Using basename as program_basename isn't available here
        'output_program': '{basename}_program_fixed{ext}',
    },
    'trace': {'output': '{basename}_trace_results.log'},
    'bug': {'output': 'test_{basename}_bug{ext}'},
    'auto-deps': {'output': '{basename}_with_deps.prompt'},
    'verify': {
        'output_results': '{basename}_verify_results.log',
        'output_code': '{basename}_verified{ext}',
        'output_program': '{basename}_program_verified{ext}',
    },
}

# Define the mapping from command/output key to environment variables
ENV_VAR_MAP: Dict[str, Dict[str, str]] = {
    'generate': {'output': 'PDD_GENERATE_OUTPUT_PATH'},
    'example': {'output': 'PDD_EXAMPLE_OUTPUT_PATH'},
    'test': {'output': 'PDD_TEST_OUTPUT_PATH'},
    'preprocess': {'output': 'PDD_PREPROCESS_OUTPUT_PATH'},
    'fix': {
        'output_test': 'PDD_FIX_TEST_OUTPUT_PATH',
        'output_code': 'PDD_FIX_CODE_OUTPUT_PATH',
        'output_results': 'PDD_FIX_RESULTS_OUTPUT_PATH',
    },
    'split': {
        'output_sub': 'PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH',
        'output_modified': 'PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH',
    },
    'change': {'output': 'PDD_CHANGE_OUTPUT_PATH'},
    'update': {'output': 'PDD_UPDATE_OUTPUT_PATH'},
    'detect': {'output': 'PDD_DETECT_OUTPUT_PATH'},
    'conflicts': {'output': 'PDD_CONFLICTS_OUTPUT_PATH'},
    'crash': {
        'output': 'PDD_CRASH_OUTPUT_PATH',
        'output_program': 'PDD_CRASH_PROGRAM_OUTPUT_PATH',
    },
    'trace': {'output': 'PDD_TRACE_OUTPUT_PATH'},
    'bug': {'output': 'PDD_BUG_OUTPUT_PATH'},
    'auto-deps': {'output': 'PDD_AUTO_DEPS_OUTPUT_PATH'},
    'verify': {
        'output_results': 'PDD_VERIFY_RESULTS_OUTPUT_PATH',
        'output_code': 'PDD_VERIFY_CODE_OUTPUT_PATH',
        'output_program': 'PDD_VERIFY_PROGRAM_OUTPUT_PATH',
    },
}

# --- Helper Function ---

def _get_default_filename(command: str, output_key: str, basename: str, language: str, file_extension: str) -> str:
    """Generates the default filename based on the command and output key."""
    try:
        pattern = DEFAULT_FILENAMES[command][output_key]
        # Use specific extension if in pattern, otherwise use language extension
        if '{ext}' in pattern:
             # Ensure file_extension starts with '.' if not empty
            effective_extension = file_extension if file_extension.startswith('.') or not file_extension else '.' + file_extension
            return pattern.format(basename=basename, language=language, ext=effective_extension)
        else:
            # Pattern already contains the full extension (e.g., .prompt, .log, .csv)
             return pattern.format(basename=basename, language=language) # ext might not be needed
    except KeyError:
        logger.error(f"Default filename pattern not found for command '{command}', output key '{output_key}'.")
        # Fallback or raise error - returning a basic fallback for now
        return f"{basename}_{output_key}_default{file_extension}"
    except Exception as e:
        logger.error(f"Error formatting default filename for {command}/{output_key}: {e}")
        return f"{basename}_{output_key}_error{file_extension}"

# --- Main Function ---

def generate_output_paths(
    command: str,
    output_locations: Dict[str, Optional[str]],
    basename: str,
    language: str,
    file_extension: str
) -> Dict[str, str]:
    """
    Generates the full, absolute output paths for a given PDD command.

    It prioritizes user-specified paths (--output options), then environment
    variables, and finally falls back to default naming conventions in the
    current working directory.

    Args:
        command: The PDD command being executed (e.g., 'generate', 'fix').
        output_locations: Dictionary of user-specified output locations from
                          command-line options (e.g., {'output': 'path/to/file',
                          'output_test': 'dir/'}). Keys use underscores.
                          Values can be None if the option wasn't provided.
        basename: The base name derived from the input prompt file.
        language: The programming language associated with the operation.
        file_extension: The file extension (including '.') for the language,
                        used when default patterns require it.

    Returns:
        A dictionary where keys are the standardized output identifiers
        (e.g., 'output', 'output_test') and values are the full, absolute
        paths to the determined output files. Returns an empty dictionary
        if the command is unknown.
    """
    logger.debug(f"Generating output paths for command: {command}")
    logger.debug(f"User output locations: {output_locations}")
    logger.debug(f"Basename: {basename}, Language: {language}, Extension: {file_extension}")

    result_paths: Dict[str, str] = {}

    if not basename:
        logger.error("Basename is required but was not provided.")
        return {} # Cannot generate paths without a basename

    # Ensure file_extension starts with '.' if provided
    if file_extension and not file_extension.startswith('.'):
        file_extension = '.' + file_extension
        logger.debug(f"Adjusted file extension to: {file_extension}")


    expected_output_keys = COMMAND_OUTPUT_KEYS.get(command)
    if not expected_output_keys:
        logger.error(f"Unknown command '{command}' provided.")
        return {}

    # Ensure the input output_locations dictionary uses underscores
    # (This should ideally be handled by the argument parser, but double-check)
    processed_output_locations = {k.replace('-', '_'): v for k, v in output_locations.items()}


    for output_key in expected_output_keys:
        logger.debug(f"Processing output key: {output_key}")

        user_path: Optional[str] = processed_output_locations.get(output_key)
        env_var_name: Optional[str] = ENV_VAR_MAP.get(command, {}).get(output_key)
        env_path: Optional[str] = os.environ.get(env_var_name) if env_var_name else None

        # Generate the default filename for this specific output key
        default_filename = _get_default_filename(command, output_key, basename, language, file_extension)
        logger.debug(f"Default filename for {output_key}: {default_filename}")


        final_path: Optional[str] = None
        source: str = "default" # Track where the path came from

        # 1. Check User-Specified Path (--output option)
        if user_path:
            source = "user"
            # Check if the user provided a directory path
            # Ends with separator OR is an existing directory
            is_dir = user_path.endswith(os.path.sep)
            if not is_dir:
                 try:
                     # Check if it exists and is a directory, suppressing errors if it doesn't exist yet
                     if os.path.exists(user_path) and os.path.isdir(user_path):
                         is_dir = True
                 except Exception as e:
                     logger.warning(f"Could not check if user path '{user_path}' is a directory: {e}")

            if is_dir:
                logger.debug(f"User path '{user_path}' identified as a directory.")
                final_path = os.path.join(user_path, default_filename)
            else:
                logger.debug(f"User path '{user_path}' identified as a specific file path.")
                final_path = user_path # Assume it's a full path or filename

        # 2. Check Environment Variable Path
        elif env_path:
            source = "environment"
            # Check if the environment variable points to a directory
            is_dir = env_path.endswith(os.path.sep)
            if not is_dir:
                 try:
                     if os.path.exists(env_path) and os.path.isdir(env_path):
                         is_dir = True
                 except Exception as e:
                     logger.warning(f"Could not check if env path '{env_path}' is a directory: {e}")

            if is_dir:
                logger.debug(f"Env path '{env_path}' identified as a directory.")
                final_path = os.path.join(env_path, default_filename)
            else:
                logger.debug(f"Env path '{env_path}' identified as a specific file path.")
                final_path = env_path # Assume it's a full path or filename

        # 3. Use Default Naming Convention in CWD
        else:
            source = "default"
            logger.debug(f"Using default filename '{default_filename}' in current directory.")
            final_path = default_filename # Relative to CWD initially

        # Resolve to absolute path
        if final_path:
            try:
                absolute_path = os.path.abspath(final_path)
                result_paths[output_key] = absolute_path
                logger.info(f"Determined path for '{output_key}' ({source}): {absolute_path}")
            except Exception as e:
                 logger.error(f"Failed to resolve path '{final_path}' to absolute path: {e}")
                 # Decide how to handle: skip, use relative, raise error? Using relative for now.
                 result_paths[output_key] = final_path
                 logger.warning(f"Using relative path for '{output_key}' due to error: {final_path}")

        else:
             logger.error(f"Could not determine a final path for output key '{output_key}' for command '{command}'.")


    logger.debug(f"Final generated paths: {result_paths}")
    return result_paths

# --- Example Usage (for testing) ---
if __name__ == '__main__':
    # Mock inputs
    mock_basename = "my_module"
    mock_language = "python"
    mock_extension = ".py"

    # --- Test Case 1: Generate command, no user/env input ---
    print("\n--- Test Case 1: Generate (Defaults) ---")
    paths1 = generate_output_paths(
        command='generate',
        output_locations={}, # No user input
        basename=mock_basename,
        language=mock_language,
        file_extension=mock_extension
    )
    print(f"Result: {paths1}")
    # Expected: {'output': '/path/to/cwd/my_module.py'}

    # --- Test Case 2: Generate command, user specifies filename ---
    print("\n--- Test Case 2: Generate (User Filename) ---")
    paths2 = generate_output_paths(
        command='generate',
        output_locations={'output': 'generated_code.py'},
        basename=mock_basename,
        language=mock_language,
        file_extension=mock_extension
    )
    print(f"Result: {paths2}")
    # Expected: {'output': '/path/to/cwd/generated_code.py'}

    # --- Test Case 3: Generate command, user specifies directory ---
    print("\n--- Test Case 3: Generate (User Directory) ---")
    # Create a dummy directory for testing
    test_dir_gen = "temp_gen_output"
    os.makedirs(test_dir_gen, exist_ok=True)
    paths3 = generate_output_paths(
        command='generate',
        output_locations={'output': test_dir_gen + os.path.sep}, # Explicit directory
        basename=mock_basename,
        language=mock_language,
        file_extension=mock_extension
    )
    print(f"Result: {paths3}")
    # Expected: {'output': '/path/to/cwd/temp_gen_output/my_module.py'}
    os.rmdir(test_dir_gen) # Clean up

    # --- Test Case 4: Fix command, mixed user input (dir and file) ---
    print("\n--- Test Case 4: Fix (Mixed User Input) ---")
    test_dir_fix = "temp_fix_tests"
    os.makedirs(test_dir_fix, exist_ok=True)
    paths4 = generate_output_paths(
        command='fix',
        output_locations={
            'output_test': test_dir_fix, # Directory
            'output_code': 'src/fixed_code.py', # Specific file
            'output_results': None # Use default/env
        },
        basename=mock_basename,
        language=mock_language,
        file_extension=mock_extension
    )
    print(f"Result: {paths4}")
    # Expected: {
    #   'output_test': '/path/to/cwd/temp_fix_tests/test_my_module_fixed.py',
    #   'output_code': '/path/to/cwd/src/fixed_code.py',
    #   'output_results': '/path/to/cwd/my_module_fix_results.log'
    # }
    os.rmdir(test_dir_fix) # Clean up

    # --- Test Case 5: Fix command, using environment variables ---
    print("\n--- Test Case 5: Fix (Environment Variables) ---")
    test_dir_env_code = "env_fixed_code_dir"
    test_dir_env_results = "env_results_dir"
    os.makedirs(test_dir_env_code, exist_ok=True)
    os.makedirs(test_dir_env_results, exist_ok=True)
    # Set mock environment variables
    os.environ['PDD_FIX_CODE_OUTPUT_PATH'] = test_dir_env_code + os.path.sep # Directory
    os.environ['PDD_FIX_RESULTS_OUTPUT_PATH'] = os.path.join(test_dir_env_results, "custom_fix_log.txt") # Specific file

    paths5 = generate_output_paths(
        command='fix',
        output_locations={}, # No user input
        basename=mock_basename,
        language=mock_language,
        file_extension=mock_extension
    )
    print(f"Result: {paths5}")
    # Expected: {
    #   'output_test': '/path/to/cwd/test_my_module_fixed.py', # Default
    #   'output_code': '/path/to/cwd/env_fixed_code_dir/my_module_fixed.py', # Env Dir
    #   'output_results': '/path/to/cwd/env_results_dir/custom_fix_log.txt' # Env File
    # }
    # Clean up env vars and dirs
    del os.environ['PDD_FIX_CODE_OUTPUT_PATH']
    del os.environ['PDD_FIX_RESULTS_OUTPUT_PATH']
    os.rmdir(test_dir_env_code)
    os.rmdir(test_dir_env_results)

    # --- Test Case 6: Preprocess command (fixed extension) ---
    print("\n--- Test Case 6: Preprocess (Fixed Extension) ---")
    paths6 = generate_output_paths(
        command='preprocess',
        output_locations={},
        basename=mock_basename,
        language=mock_language,
        file_extension=mock_extension # This extension is ignored for preprocess default
    )
    print(f"Result: {paths6}")
    # Expected: {'output': '/path/to/cwd/my_module_python_preprocessed.prompt'}

    # --- Test Case 7: Unknown command ---
    print("\n--- Test Case 7: Unknown Command ---")
    paths7 = generate_output_paths(
        command='nonexistent',
        output_locations={},
        basename=mock_basename,
        language=mock_language,
        file_extension=mock_extension
    )
    print(f"Result: {paths7}")
    # Expected: {}

    # --- Test Case 8: Split command defaults ---
    print("\n--- Test Case 8: Split (Defaults) ---")
    paths8 = generate_output_paths(
        command='split',
        output_locations={},
        basename="complex_prompt",
        language="javascript",
        file_extension=".js" # Ignored for split defaults
    )
    print(f"Result: {paths8}")
    # Expected: {
    #   'output_sub': '/path/to/cwd/sub_complex_prompt.prompt',
    #   'output_modified': '/path/to/cwd/modified_complex_prompt.prompt'
    # }

    # --- Test Case 9: Detect command default (using basename) ---
    print("\n--- Test Case 9: Detect (Default) ---")
    paths9 = generate_output_paths(
        command='detect',
        output_locations={},
        basename="feature_analysis", # Used instead of change_file_basename
        language="", # Not relevant for detect default
        file_extension="" # Not relevant for detect default
    )
    print(f"Result: {paths9}")
    # Expected: {'output': '/path/to/cwd/feature_analysis_detect.csv'}

    # --- Test Case 10: Crash command defaults (using basename) ---
    print("\n--- Test Case 10: Crash (Defaults) ---")
    paths10 = generate_output_paths(
        command='crash',
        output_locations={},
        basename="crashed_module", # Used for both code and program defaults
        language="java",
        file_extension=".java"
    )
    print(f"Result: {paths10}")
    # Expected: {
    #   'output': '/path/to/cwd/crashed_module_fixed.java',
    #   'output_program': '/path/to/cwd/crashed_module_program_fixed.java'
    # }

    # --- Test Case 11: Verify command defaults ---
    print("\n--- Test Case 11: Verify (Defaults) ---")
    paths11 = generate_output_paths(
        command='verify',
        output_locations={},
        basename="module_to_verify",
        language="python",
        file_extension=".py"
    )
    print(f"Result: {paths11}")
    # Expected: {
    #   'output_results': '/path/to/cwd/module_to_verify_verify_results.log',
    #   'output_code': '/path/to/cwd/module_to_verify_verified.py'
    #   'output_program': '/path/to/cwd/module_to_verify_program_verified.py'
    # }

    # --- Test Case 12: Verify command with user-specified output_program directory ---
    print("\n--- Test Case 12: Verify (User Dir for output_program) ---")
    test_dir_verify_prog = "temp_verify_prog_output"
    os.makedirs(test_dir_verify_prog, exist_ok=True)
    paths12 = generate_output_paths(
        command='verify',
        output_locations={'output_program': test_dir_verify_prog + os.path.sep},
        basename="module_to_verify",
        language="python",
        file_extension=".py"
    )
    print(f"Result: {paths12}")
    # Expected: {
    #   'output_results': '/path/to/cwd/module_to_verify_verify_results.log',
    #   'output_code': '/path/to/cwd/module_to_verify_verified.py',
    #   'output_program': f'/path/to/cwd/{test_dir_verify_prog}/module_to_verify_program_verified.py'
    # }
    os.rmdir(test_dir_verify_prog) # Clean up

    # --- Test Case 13: Verify command with environment variable for output_program ---
    print("\n--- Test Case 13: Verify (Env Var for output_program) ---")
    env_verify_prog_path = "env_verify_program_custom.py"
    os.environ['PDD_VERIFY_PROGRAM_OUTPUT_PATH'] = env_verify_prog_path
    paths13 = generate_output_paths(
        command='verify',
        output_locations={},
        basename="another_module_verify",
        language="python",
        file_extension=".py"
    )
    print(f"Result: {paths13}")
    # Expected: {
    #   'output_results': '/path/to/cwd/another_module_verify_verify_results.log',
    #   'output_code': '/path/to/cwd/another_module_verify_verified.py',
    #   'output_program': f'/path/to/cwd/{env_verify_prog_path}'
    # }
    del os.environ['PDD_VERIFY_PROGRAM_OUTPUT_PATH'] # Clean up