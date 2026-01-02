import os
import logging
from typing import Dict, List, Literal, Optional

# Type alias for path resolution mode
PathResolutionMode = Literal["config_base", "cwd"]

# Configure logging
logger = logging.getLogger(__name__)

# --- Configuration Data ---

# Default directory names
EXAMPLES_DIR = "examples"

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
    'sync': ['generate_output_path', 'test_output_path', 'example_output_path'],
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
    'detect': {'output': '{basename}_detect.csv'}, # basename here is from change_file per construct_paths logic
    'conflicts': {'output': '{basename}_conflict.csv'}, # basename here is combined sorted prompt basenames per construct_paths logic
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
    'sync': {
        'generate_output_path': '{basename}{ext}',
        'test_output_path': 'test_{basename}{ext}',
        'example_output_path': '{basename}_example{ext}',
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
    'sync': {
        'generate_output_path': 'PDD_GENERATE_OUTPUT_PATH',
        'test_output_path': 'PDD_TEST_OUTPUT_PATH',
        'example_output_path': 'PDD_EXAMPLE_OUTPUT_PATH',
    },
}

# Define mapping from context config keys to output keys for different commands
CONTEXT_CONFIG_MAP: Dict[str, Dict[str, str]] = {
    'generate': {'output': 'generate_output_path'},
    'example': {'output': 'example_output_path'},
    'test': {'output': 'test_output_path'},
    'sync': {
        'generate_output_path': 'generate_output_path',
        'test_output_path': 'test_output_path',
        'example_output_path': 'example_output_path',
    },
    # For other commands, they can use the general mapping if needed
    'preprocess': {'output': 'generate_output_path'},  # fallback
    'fix': {
        'output_test': 'test_output_path',
        'output_code': 'generate_output_path',
        'output_results': 'generate_output_path',  # fallback for results
    },
    'split': {
        'output_sub': 'generate_output_path',      # fallback
        'output_modified': 'generate_output_path', # fallback
    },
    'change': {'output': 'generate_output_path'},
    'update': {'output': 'generate_output_path'},
    'detect': {'output': 'generate_output_path'},
    'conflicts': {'output': 'generate_output_path'},
    'crash': {
        'output': None,  # Use default CWD behavior, not context paths
        'output_program': None,  # Use default CWD behavior, not context paths
    },
    'trace': {'output': 'generate_output_path'},
    'bug': {'output': 'test_output_path'},
    'auto-deps': {'output': 'generate_output_path'},
    'verify': {
        'output_results': 'generate_output_path',
        'output_code': 'generate_output_path',
        'output_program': 'generate_output_path',
    },
}

# --- Helper Function ---

def _get_default_filename(command: str, output_key: str, basename: str, language: str, file_extension: str) -> str:
    """Generates the default filename based on the command and output key.

    Supports subdirectory basenames like 'core/cloud'. When the basename contains
    a forward slash, the directory structure is preserved in the output:
    - Directory part (e.g., 'core/') is prepended to the final filename
    - Pattern is applied only to the name part (e.g., 'cloud')

    Example: basename='core/cloud', pattern='test_{basename}{ext}'
    Result: 'core/test_cloud.py' (NOT 'test_core/cloud.py')
    """
    try:
        # Split basename into directory and name components for subdirectory support
        if '/' in basename:
            dir_part, name_part = basename.rsplit('/', 1)
            dir_prefix = dir_part + '/'
        else:
            dir_prefix = ''
            name_part = basename

        pattern = DEFAULT_FILENAMES[command][output_key]

        # Use specific extension if in pattern, otherwise use language extension
        if '{ext}' in pattern:
            # Ensure file_extension starts with '.' if not empty
            effective_extension = file_extension if file_extension.startswith('.') or not file_extension else '.' + file_extension
            filename = pattern.format(basename=name_part, language=language, ext=effective_extension)
        else:
            # Pattern already contains the full extension (e.g., .prompt, .log, .csv)
            filename = pattern.format(basename=name_part, language=language)

        # Prepend directory part to preserve subdirectory structure
        return dir_prefix + filename
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
    file_extension: str,
    context_config: Optional[Dict[str, str]] = None,
    input_file_dir: Optional[str] = None,
    input_file_dirs: Optional[Dict[str, str]] = None,
    config_base_dir: Optional[str] = None,
    path_resolution_mode: PathResolutionMode = "config_base",
) -> Dict[str, str]:
    """
    Generates the full, absolute output paths for a given PDD command.

    It prioritizes user-specified paths (--output options), then context
    configuration from .pddrc, then environment variables, and finally
    falls back to default naming conventions in the input file's directory
    (or current working directory if input_file_dir is not provided).

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
        context_config: Optional dictionary with context-specific paths from .pddrc
                       configuration (e.g., {'generate_output_path': 'src/'}).
        input_file_dir: Optional path to the input file's directory. When provided,
                       default output files will be placed in this directory instead
                       of the current working directory.
        input_file_dirs: Optional dictionary mapping output keys to specific input
                         file directories. When provided, each output will use its
                         corresponding input file directory (e.g., {'output_code': 'src/main/java'}).
        config_base_dir: Optional base directory to resolve relative `.pddrc` and
                        environment variable output paths. When set, relative
                        config paths resolve under this directory (typically the
                        directory containing `.pddrc`) instead of the input file
                        directory.
        path_resolution_mode: Controls how relative paths from `.pddrc` and
                             environment variables are resolved. "config_base"
                             (default) resolves relative to config_base_dir,
                             "cwd" resolves relative to the current working
                             directory. Use "cwd" for sync command to ensure
                             output files are created where the user is.

    Returns:
        A dictionary where keys are the standardized output identifiers
        (e.g., 'output', 'output_test') and values are the full, absolute
        paths to the determined output files. Returns an empty dictionary
        if the command is unknown.
    """
    logger.debug(f"Generating output paths for command: {command}")
    logger.debug(f"User output locations: {output_locations}")
    logger.debug(f"Context config: {context_config}")
    logger.debug(f"Input file dirs: {input_file_dirs}")
    logger.debug(f"Config base dir: {config_base_dir}")
    logger.debug(f"Path resolution mode: {path_resolution_mode}")
    logger.debug(f"Basename: {basename}, Language: {language}, Extension: {file_extension}")

    context_config = context_config or {}
    input_file_dirs = input_file_dirs or {}
    config_base_dir_abs = os.path.abspath(config_base_dir) if config_base_dir else None
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
        
        # Get context configuration path for this output key
        context_config_key = CONTEXT_CONFIG_MAP.get(command, {}).get(output_key)
        context_path: Optional[str] = context_config.get(context_config_key) if context_config_key else None
        
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

        # 2. Check Context Configuration Path (.pddrc)
        elif context_path:
            source = "context"

            # Resolve relative `.pddrc` paths based on path_resolution_mode.
            # "cwd" mode: resolve relative to current working directory (for sync)
            # "config_base" mode: resolve relative to config_base_dir (for fix, etc.)
            # Fall back to the input file directory for backwards compatibility.
            if not os.path.isabs(context_path):
                if path_resolution_mode == "cwd":
                    context_path = os.path.join(os.getcwd(), context_path)
                elif config_base_dir_abs:
                    context_path = os.path.join(config_base_dir_abs, context_path)
                elif input_file_dir:
                    context_path = os.path.join(input_file_dir, context_path)
                logger.debug(f"Resolved relative context path to: {context_path}")

            # Check if the context path is a directory
            is_dir = context_path.endswith(os.path.sep) or context_path.endswith('/')
            if not is_dir:
                 try:
                     if os.path.exists(context_path) and os.path.isdir(context_path):
                         is_dir = True
                 except Exception as e:
                     logger.warning(f"Could not check if context path '{context_path}' is a directory: {e}")

            if is_dir:
                logger.debug(f"Context path '{context_path}' identified as a directory.")
                final_path = os.path.join(context_path, default_filename)
            else:
                logger.debug(f"Context path '{context_path}' identified as a specific file path.")
                final_path = context_path

        # 3. Check Environment Variable Path
        elif env_path:
            source = "environment"

            # Resolve relative env paths based on path_resolution_mode.
            # Same logic as .pddrc paths for consistency.
            if not os.path.isabs(env_path):
                if path_resolution_mode == "cwd":
                    env_path = os.path.join(os.getcwd(), env_path)
                elif config_base_dir_abs:
                    env_path = os.path.join(config_base_dir_abs, env_path)
                elif input_file_dir:
                    env_path = os.path.join(input_file_dir, env_path)
                logger.debug(f"Resolved relative env path to: {env_path}")

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

        # 4. Use Default Naming Convention
        else:
            source = "default"
            # For example command, default to examples/ directory if no .pddrc config
            if command == "example":
                examples_dir = EXAMPLES_DIR  # Fallback constant
                # Create examples directory if it doesn't exist
                try:
                    os.makedirs(examples_dir, exist_ok=True)
                    logger.debug(f"Created examples directory: {examples_dir}")
                except OSError as e:
                    logger.warning(f"Could not create examples directory: {e}")
                final_path = os.path.join(examples_dir, default_filename)
                logger.debug(f"Using default filename '{default_filename}' in examples directory.")
            else:
                # First check if there's a specific directory for this output key
                specific_dir = input_file_dirs.get(output_key)
                if specific_dir:
                    final_path = os.path.join(specific_dir, default_filename)
                    logger.debug(f"Using default filename '{default_filename}' in specific input file directory: {specific_dir}")
                # Otherwise use the general input file directory if provided
                elif input_file_dir:
                    final_path = os.path.join(input_file_dir, default_filename)
                    logger.debug(f"Using default filename '{default_filename}' in input file directory: {input_file_dir}")
                else:
                    final_path = default_filename # Relative to CWD initially
                    logger.debug(f"Using default filename '{default_filename}' in current directory.")

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
    # Configure logging for standalone execution
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

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
        file_extension=mock_extension,
        context_config={}
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
        file_extension=mock_extension,
        context_config={}
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
        file_extension=mock_extension,
        context_config={}
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
        file_extension=mock_extension,
        context_config={}
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
        file_extension=mock_extension,
        context_config={}
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
        file_extension=mock_extension, # This extension is ignored for preprocess default
        context_config={}
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
        file_extension=mock_extension,
        context_config={}
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
        file_extension=".js", # Ignored for split defaults
        context_config={}
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
        file_extension="", # Not relevant for detect default
        context_config={}
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
        file_extension=".java",
        context_config={}
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
        file_extension=".py",
        context_config={}
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
        file_extension=".py",
        context_config={}
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
        file_extension=".py",
        context_config={}
    )
    print(f"Result: {paths13}")
    # Expected: {
    #   'output_results': '/path/to/cwd/another_module_verify_verify_results.log',
    #   'output_code': '/path/to/cwd/another_module_verify_verified.py',
    #   'output_program': f'/path/to/cwd/{env_verify_prog_path}'
    # }
    del os.environ['PDD_VERIFY_PROGRAM_OUTPUT_PATH'] # Clean up
