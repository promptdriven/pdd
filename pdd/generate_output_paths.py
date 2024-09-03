import os
from pathlib import Path
from typing import Dict, Any


def generate_output_paths(command: str, output_locations: Dict[str, str], basename: str, language: str, file_extension: str) -> Dict[str, str]:
    """
    Generate output paths based on the command and provided parameters.

    :param command: The command for which the output path is generated.
    :param output_locations: A dictionary of output locations.
    :param basename: The base name for the output file.
    :param language: The programming language for the output file.
    :param file_extension: The file extension for the output file.
    :return: A dictionary with the generated output paths.
    """
    result = {}

    def process_output(key: str, default_name: str) -> str:
        """
        Process the output path based on the key and default name.

        :param key: The key to look up in output_locations.
        :param default_name: The default name to use if no path is found.
        :return: The resolved output path.
        """
        try:
            if key in output_locations:
                path = output_locations[key]
                if path:
                    if os.path.isdir(path):
                        return os.path.join(path, default_name)
                    return path

            env_var = f"PDD_{command.upper()}_OUTPUT_PATH"
            if key != 'output':
                env_var += f"_{key.split('_')[-1].upper()}"

            env_path = os.getenv(env_var)
            if env_path:
                return os.path.join(env_path, default_name)

            return default_name
        except Exception as e:
            print(f"Error processing output for {key}: {e}")
            return default_name

    if command == 'generate':
        result['output'] = process_output('output', f"{basename}{file_extension}")

    elif command == 'example':
        result['output'] = process_output('output', f"{basename}_example{file_extension}")

    elif command == 'test':
        result['output'] = process_output('output', f"test_{basename}{file_extension}")

    elif command == 'preprocess':
        result['output'] = process_output('output', f"{basename}_{language}_preprocessed.prompt")

    elif command == 'fix':
        result['output_test'] = process_output('output_test', f"test_{basename}_fixed{file_extension}")
        result['output_code'] = process_output('output_code', f"{basename}_fixed{file_extension}")

    elif command == 'split':
        result['output_sub'] = process_output('output_sub', f"sub_{basename}.prompt")
        result['output_modified'] = process_output('output_modified', f"modified_{basename}.prompt")

    elif command in ['change', 'update']:
        result['output'] = process_output('output', f"modified_{basename}.prompt")

    elif command == 'detect':
        result['output'] = process_output('output', f"{basename}_detect.csv")

    elif command == 'conflicts':
        result['output'] = process_output('output', f"{basename}_conflict.csv")

    elif command == 'crash':
        result['output'] = process_output('output', f"{basename}_fixed{file_extension}")

    return result
