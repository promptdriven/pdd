import os
from pathlib import Path
from typing import Dict, Union


def generate_output_paths(command: str, output_locations: Dict[str, str], basename: str, language: str, file_extension: str) -> Dict[str, str]:
    """
    Generate output paths based on the command, output locations, basename, language, and file extension.

    :param command: The command for which the output path is being generated.
    :param output_locations: A dictionary of output locations provided by the user.
    :param basename: The base name for the output file.
    :param language: The programming language of the output file.
    :param file_extension: The file extension for the output file.
    :return: A dictionary with the appropriate output paths for each command.
    """
    result = {}

    # Define default naming conventions
    default_names = {
        'generate': f"{basename}{file_extension}",
        'example': f"{basename}_example{file_extension}",
        'test': f"test_{basename}{file_extension}",
        'preprocess': f"{basename}_{language}_preprocessed.prompt",
        'fix': {
            'output_test': f"test_{basename}_fixed{file_extension}",
            'output_code': f"{basename}_fixed{file_extension}"
        },
        'split': {
            'output_sub': f"sub_{basename}.prompt",
            'output_modified': f"modified_{basename}.prompt"
        },
        'change': f"modified_{basename}.prompt",
        'update': f"modified_{basename}.prompt",
        'detect': f"{basename}_detect.csv",
        'conflicts': f"{basename}_conflict.csv",
        'crash': f"{basename}_fixed{file_extension}"
    }

    # Define environment variables for each command
    env_vars = {
        'generate': 'PDD_GENERATE_OUTPUT_PATH',
        'example': 'PDD_EXAMPLE_OUTPUT_PATH',
        'test': 'PDD_TEST_OUTPUT_PATH',
        'preprocess': 'PDD_PREPROCESS_OUTPUT_PATH',
        'fix': {
            'output_test': 'PDD_FIX_TEST_OUTPUT_PATH',
            'output_code': 'PDD_FIX_CODE_OUTPUT_PATH'
        },
        'split': {
            'output_sub': 'PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH',
            'output_modified': 'PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH'
        },
        'change': 'PDD_CHANGE_OUTPUT_PATH',
        'update': 'PDD_UPDATE_OUTPUT_PATH',
        'detect': 'PDD_DETECT_OUTPUT_PATH',
        'conflicts': 'PDD_CONFLICTS_OUTPUT_PATH',
        'crash': 'PDD_CRASH_OUTPUT_PATH'
    }

    def get_output_path(key: str) -> str:
        """
        Determine the output path for a given key based on output locations, environment variables, and default names.

        :param key: The key for which the output path is being determined.
        :return: The determined output path as a string.
        """
        if key in output_locations and output_locations[key]:
            path = Path(output_locations[key])
            if path.is_dir():
                return str(path / default_names[command])
            return str(path)

        env_var = env_vars[command]
        if isinstance(env_var, dict):
            env_var = env_var[key]

        if env_var in os.environ:
            path = Path(os.environ[env_var])
            if path.is_dir():
                return str(path / default_names[command])
            return str(path)

        return default_names[command]

    if command in ['fix', 'split']:
        for key in default_names[command].keys():
            result[key] = get_output_path(key)
    else:
        result['output'] = get_output_path('output')

    return result
