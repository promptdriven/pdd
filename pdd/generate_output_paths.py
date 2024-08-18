from pathlib import Path
from typing import Dict, Optional, Union
import os


def generate_output_paths(
    command: str,
    output_locations: Dict[str, Optional[str]],
    basename: str,
    language: str,
    file_extension: str
) -> Dict[str, str]:
    """
    Generate output paths for various PDD commands.

    This function determines the appropriate output paths based on the command,
    user-specified output locations, and environment variables.

    Args:
        command (str): The PDD command being executed.
        output_locations (Dict[str, Optional[str]]): User-specified output locations.
        basename (str): The base name of the file.
        language (str): The programming language of the file.
        file_extension (str): The file extension to be used.

    Returns:
        Dict[str, str]: A dictionary of output keys to their full path strings.

    Raises:
        ValueError: If an unknown command is provided.
    """
    result: Dict[str, str] = {}
    env_var_prefix = "PDD_"

    def get_default_filename(cmd: str) -> Union[str, Dict[str, str]]:
        """
        Determine the default filename(s) for a given command.

        Args:
            cmd (str): The PDD command.

        Returns:
            Union[str, Dict[str, str]]: The default filename or a dictionary of default filenames.

        Raises:
            ValueError: If an unknown command is provided.
        """
        
        if cmd == "generate":
            return f"{basename}{file_extension}"
        elif cmd == "example":
            return f"{basename}_example{file_extension}"
        elif cmd == "test":
            return f"test_{basename}{file_extension}"
        elif cmd == "preprocess":
            return f"{basename}_{language}_preprocessed.prompt"
        elif cmd == "fix":
            return {
                "output-test": f"test_{basename}_fixed{file_extension}",
                "output-code": f"{basename}_fixed{file_extension}"
            }
        elif cmd == "split":
            return {
                "output-sub": f"sub_{basename}.prompt",
                "output-modified": f"modified_{basename}.prompt",
                "output-cost": f"cost_{basename}.txt"
            }
        else:
            raise ValueError(f"Unknown command: {cmd}")

    try:
        default_filenames = get_default_filename(command)

        for key, value in output_locations.items():
            # Determine the appropriate environment variable name
            if command == "generate":
                env_var_name = f"{env_var_prefix}GENERATE_OUTPUT_PATH"
            elif command == "split":
                # Use specific naming convention for split command
                split_env_vars = {
                    "output-sub": "SUB_PROMPT",
                    "output-modified": "MODIFIED_PROMPT",
                    "output-cost": "COST"
                }
                env_var_name = f"{env_var_prefix}SPLIT_{split_env_vars.get(key, key.upper().replace('-', '_'))}_OUTPUT_PATH"
            else:
                env_var_name = f"{env_var_prefix}{command.upper()}_{key.upper().replace('-', '_')}_OUTPUT_PATH"

            # Determine the default filename for this output
            if isinstance(default_filenames, dict):
                default_filename = default_filenames.get(key, f"{basename}_{key}.{file_extension}")
            else:
                default_filename = default_filenames

            # Determine the output path
            env_value = os.environ.get(env_var_name)
            if env_value:
                # Use the environment variable if available
                result[key] = str(Path(env_value) / default_filename)
            elif value:
                # Use the user-specified path if provided
                path = Path(value)
                if path.suffix:  # If the path includes a filename
                    result[key] = str(path)
                else:
                    result[key] = str(path / default_filename)
            else:
                # Fall back to the default filename in the current directory
                result[key] = default_filename

    except Exception as e:
        # Log the error and re-raise it
        print(f"An error occurred while generating output paths: {str(e)}")
        raise

    return result