import os
from pathlib import Path

def generate_output_paths(command, output_locations, basename, language, file_extension):
    """
    Generates output filenames based on command, output_locations, basename, language, and file_extension.

    Args:
        command (str): The command being executed.
        output_locations (dict): Dictionary of output locations specified by the user.
        basename (str): The base name of the file.
        language (str): The programming language.
        file_extension (str): The file extension, including the leading dot (e.g., ".py").

    Returns:
        dict: A dictionary containing the generated output filenames with full paths.
    """
    output_paths = {}
    default_keys = {
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
        'auto-deps': ['output']
    }

    # Ensure output_locations has all necessary keys for the given command
    for key in default_keys.get(command, []):
        if key not in output_locations:
            output_locations[key] = None

    if command == 'generate':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_GENERATE_OUTPUT_PATH',
            f"{basename}{file_extension}"
        )
    elif command == 'example':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_EXAMPLE_OUTPUT_PATH',
            f"{basename}_example{file_extension}"
        )
    elif command == 'test':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_TEST_OUTPUT_PATH',
            f"test_{basename}{file_extension}"
        )
    elif command == 'preprocess':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_PREPROCESS_OUTPUT_PATH',
            f"{basename}_{language}_preprocessed.prompt"
        )
    elif command == 'fix':
        output_paths['output_test'] = get_output_path(
            output_locations.get('output_test'),
            'PDD_FIX_TEST_OUTPUT_PATH',
            f"test_{basename}_fixed{file_extension}"
        )
        output_paths['output_code'] = get_output_path(
            output_locations.get('output_code'),
            'PDD_FIX_CODE_OUTPUT_PATH',
            f"{basename}_fixed{file_extension}"
        )
        output_paths['output_results'] = get_output_path(
            output_locations.get('output_results'),
            'PDD_FIX_RESULTS_OUTPUT_PATH',
            f"{basename}_fix_results.log"
        )
    elif command == 'split':
        output_paths['output_sub'] = get_output_path(
            output_locations.get('output_sub'),
            'PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH',
            f"sub_{basename}.prompt"
        )
        output_paths['output_modified'] = get_output_path(
            output_locations.get('output_modified'),
            'PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH',
            f"modified_{basename}.prompt"
        )
    elif command == 'change':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_CHANGE_OUTPUT_PATH',
            f"modified_{basename}.prompt"
        )
    elif command == 'update':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_UPDATE_OUTPUT_PATH',
            f"modified_{basename}.prompt"
        )
    elif command == 'detect':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_DETECT_OUTPUT_PATH',
            f"{basename}_detect.csv"
        )
    elif command == 'conflicts':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_CONFLICTS_OUTPUT_PATH',
            f"{basename}_conflict.csv"
        )
    elif command == 'crash':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_CRASH_OUTPUT_PATH',
            f"{basename}_fixed{file_extension}"
        )
        output_paths['output_program'] = get_output_path(
            output_locations.get('output_program'),
            'PDD_CRASH_PROGRAM_OUTPUT_PATH',
            f"{basename}_fixed{file_extension}"
        )
    elif command == 'trace':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_TRACE_OUTPUT_PATH',
            f"{basename}_trace_results.log"
        )
    elif command == 'bug':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_BUG_OUTPUT_PATH',
            f"test_{basename}_bug{file_extension}"
        )
    elif command == 'auto-deps':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_AUTO_DEPS_OUTPUT_PATH',
            f"{basename}_with_deps.prompt"
        )
    else:
        raise ValueError(f"Invalid command: {command}")

    return output_paths

def get_output_path(user_path, env_var, default_filename):
    """
    Determines the output path based on user input, environment variables, and default behavior.
    """
    if user_path:
        # Check if user_path is a directory
        try:
            # A path is considered a directory if:
            # 1. It ends with a separator
            # 2. It exists and is a directory
            # 3. It doesn't contain a file extension
            is_dir = (user_path.endswith(os.sep) or 
                     (os.path.exists(user_path) and os.path.isdir(user_path)) or
                     not os.path.splitext(user_path)[1])
        except (TypeError, ValueError):
            is_dir = user_path.endswith(os.sep)
            
        # If it's a directory, join with default filename
        if is_dir:
            path = os.path.join(user_path.rstrip(os.sep), default_filename)
        else:
            path = user_path
            
        # Create parent directory if needed
        try:
            parent_dir = os.path.dirname(path)
            if parent_dir:
                Path(parent_dir).mkdir(parents=True, exist_ok=True)
        except (OSError, PermissionError):
            # If we can't create the directory, just return the path
            pass
        return path
    else:
        env_path = os.environ.get(env_var)
        if env_path:
            path = os.path.join(env_path, default_filename)
            try:
                # Create parent directory if needed
                Path(env_path).mkdir(parents=True, exist_ok=True)
            except (OSError, PermissionError):
                # If we can't create the directory, just return the path
                pass
            return path
        else:
            return default_filename