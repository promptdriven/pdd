import os
import pathlib
from typing import Dict, Optional

def generate_output_paths(command: str, output_locations: Dict[str, Optional[str]], basename: str, language: str, file_extension: str) -> Dict[str, str]:
    """
    Generate output paths based on the command, output locations, and other parameters.

    :param command: The command type which determines the naming convention.
    :param output_locations: A dictionary of output locations specified by the user.
    :param basename: The base name for the file.
    :param language: The programming language for the file.
    :param file_extension: The file extension for the output file.
    :return: A dictionary with keys as output types and values as the generated paths.
    """
    result = {}

    def get_default_filename(key: str) -> str:
        """Get the default filename based on the command and key."""
        if command == 'generate':
            return f"{basename}{file_extension}"
        elif command == 'example':
            return f"{basename}_example{file_extension}"
        elif command == 'test':
            return f"test_{basename}{file_extension}"
        elif command == 'preprocess':
            return f"{basename}_{language}_preprocessed.prompt"
        elif command == 'fix':
            if key == 'output_test':
                return f"test_{basename}_fixed{file_extension}"
            elif key == 'output_code':
                return f"{basename}_fixed{file_extension}"
            elif key == 'output_results':
                return f"{basename}_fix_results.log"
        elif command == 'split':
            if key == 'output_sub':
                return f"sub_{basename}.prompt"
            elif key == 'output_modified':
                return f"modified_{basename}.prompt"
        elif command in ['change', 'update']:
            return f"modified_{basename}.prompt"
        elif command == 'detect':
            return f"{basename}_detect.csv"
        elif command == 'conflicts':
            return f"{basename}_conflict.csv"
        elif command == 'crash':
            return f"{basename}_fixed{file_extension}"
        elif command == 'trace':
            return f"{basename}_trace_results.log"
        elif command == 'bug':
            return f"test_{basename}_bug{file_extension}"
        else:
            raise ValueError(f"Unrecognized command: {command}")

    def get_env_var(key: str) -> Optional[str]:
        """Get the environment variable for the given command and key."""
        env_var_map = {
            'generate': 'PDD_GENERATE_OUTPUT_PATH',
            'example': 'PDD_EXAMPLE_OUTPUT_PATH',
            'test': 'PDD_TEST_OUTPUT_PATH',
            'preprocess': 'PDD_PREPROCESS_OUTPUT_PATH',
            'fix': {
                'output_test': 'PDD_FIX_TEST_OUTPUT_PATH',
                'output_code': 'PDD_FIX_CODE_OUTPUT_PATH',
                'output_results': 'PDD_FIX_RESULTS_OUTPUT_PATH',
            },
            'split': {
                'output_sub': 'PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH',
                'output_modified': 'PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH'
            },
            'change': 'PDD_CHANGE_OUTPUT_PATH',
            'update': 'PDD_UPDATE_OUTPUT_PATH',
            'detect': 'PDD_DETECT_OUTPUT_PATH',
            'conflicts': 'PDD_CONFLICTS_OUTPUT_PATH',
            'crash': 'PDD_CRASH_OUTPUT_PATH',
            'trace': 'PDD_TRACE_OUTPUT_PATH',
            'bug': 'PDD_BUG_OUTPUT_PATH'
        }

        if command in ['fix', 'split']:
            return os.environ.get(env_var_map[command][key])
        else:
            return os.environ.get(env_var_map.get(command))

    keys = output_locations.keys() if output_locations else ['output']
    if command == 'fix':
        keys = ['output_test', 'output_code', 'output_results']
    elif command == 'split':
        keys = ['output_sub', 'output_modified']

    for key in keys:
        value = output_locations.get(key)
        if value:
            path = pathlib.Path(value)
        else:
            env_path = get_env_var(key)
            if env_path:
                path = pathlib.Path(env_path)
            else:
                result[key] = get_default_filename(key)
                continue

        if path.is_dir():
            path = path / get_default_filename(key)
        elif not path.suffix:
            # If the path doesn't have an extension, assume it's a directory
            path = path / get_default_filename(key)
        
        # Ensure the directory exists
        path.parent.mkdir(parents=True, exist_ok=True)
        
        result[key] = str(path)

    return result
