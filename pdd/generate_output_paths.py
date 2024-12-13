import os

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
        # Assuming change_file_basename is provided in output_locations for 'detect'
        change_file_basename = os.path.splitext(os.path.basename(output_locations.get('change_file')))[0]
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_DETECT_OUTPUT_PATH',
            f"{change_file_basename}_detect.csv"
        )
    elif command == 'conflicts':
        # Assuming prompt1_basename and prompt2_basename are provided in output_locations for 'conflicts'
        prompt1_basename = os.path.splitext(os.path.basename(output_locations.get('prompt1')))[0]
        prompt2_basename = os.path.splitext(os.path.basename(output_locations.get('prompt2')))[0]
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_CONFLICTS_OUTPUT_PATH',
            f"{prompt1_basename}_{prompt2_basename}_conflict.csv"
        )
    elif command == 'crash':
        output_paths['output'] = get_output_path(
            output_locations.get('output'),
            'PDD_CRASH_OUTPUT_PATH',
            f"{basename}_fixed{file_extension}"
        )
        program_basename = os.path.splitext(os.path.basename(output_locations.get('program_file')))[0]
        output_paths['output_program'] = get_output_path(
            output_locations.get('output_program'),
            'PDD_CRASH_PROGRAM_OUTPUT_PATH',
            f"{program_basename}_fixed{file_extension}"
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

    Args:
        user_path (str): The output path specified by the user.
        env_var (str): The name of the environment variable to check.
        default_filename (str): The default filename to use if no other path is specified.

    Returns:
        str: The determined output path.
    """
    if user_path:
        if user_path.endswith(os.sep) or os.path.isdir(user_path):
            # User provided a directory
            return os.path.join(user_path, default_filename)
        else:
            # User provided a filename
            return user_path
    else:
        env_path = os.environ.get(env_var)
        if env_path:
            # Environment variable is set
            return os.path.join(env_path, default_filename)
        else:
            # Default behavior: use default filename in the current working directory
            return default_filename
