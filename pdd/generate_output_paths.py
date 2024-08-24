import os
from pathlib import Path
from typing import Dict, Optional


def generate_output_paths(command: str, output_locations: Dict[str, Optional[str]], basename: str, language: str, file_extension: str) -> Dict[str, str]:
    """
    Generate output paths based on the command and provided output locations.

    :param command: The command for which to generate output paths.
    :param output_locations: A dictionary of output locations.
    :param basename: The base name for the output files.
    :param language: The programming language for the output files.
    :param file_extension: The file extension for the output files.
    :return: A dictionary with keys as output location identifiers and values as the generated paths.
    """
    result = {}

    def get_full_path(output: Optional[str], default_name: str) -> str:
        """Generate the full path for the output."""
        if not output:
            return default_name
        if os.path.isdir(output):
            return os.path.join(output, default_name)
        return output

    def get_env_var(var_name: str) -> str:
        """Get the value of an environment variable."""
        return os.environ.get(var_name, "")

    if command == "generate":
        default_name = f"{basename}{file_extension}"
        env_var = "PDD_GENERATE_OUTPUT_PATH"
    elif command == "example":
        default_name = f"{basename}_example{file_extension}"
        env_var = "PDD_EXAMPLE_OUTPUT_PATH"
    elif command == "test":
        default_name = f"test_{basename}{file_extension}"
        env_var = "PDD_TEST_OUTPUT_PATH"
    elif command == "preprocess":
        default_name = f"{basename}_{language}_preprocessed.prompt"
        env_var = "PDD_PREPROCESS_OUTPUT_PATH"
    elif command == "fix":
        test_default_name = f"test_{basename}_fixed{file_extension}"
        code_default_name = f"{basename}_fixed{file_extension}"
        test_env_var = "PDD_FIX_TEST_OUTPUT_PATH"
        code_env_var = "PDD_FIX_CODE_OUTPUT_PATH"
    elif command == "split":
        sub_default_name = f"sub_{basename}.prompt"
        modified_default_name = f"modified_{basename}.prompt"
        sub_env_var = "PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH"
        modified_env_var = "PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH"
    elif command in ["change", "update"]:
        default_name = f"modified_{basename}.prompt"
        env_var = f"PDD_{command.upper()}_OUTPUT_PATH"
    else:
        raise ValueError(f"Unknown command: {command}")

    for key, output in output_locations.items():
        if command == "fix":
            if key == "output_test":
                env_value = get_env_var(test_env_var)
                result[key] = get_full_path(output or env_value, test_default_name)
            elif key == "output_code":
                env_value = get_env_var(code_env_var)
                result[key] = get_full_path(output or env_value, code_default_name)
        elif command == "split":
            if key == "output_sub":
                env_value = get_env_var(sub_env_var)
                result[key] = get_full_path(output or env_value, sub_default_name)
            elif key == "output_modified":
                env_value = get_env_var(modified_env_var)
                result[key] = get_full_path(output or env_value, modified_default_name)
        else:
            env_value = get_env_var(env_var)
            result[key] = get_full_path(output or env_value, default_name)
            
    return result
