import os

def generate_output_paths(command, output_locations, basename, language, file_extension):
    """
    Generates output filenames based on the command, user options, and environment variables.
    
    Args:
        command (str): The command being executed.
        output_locations (dict): Dictionary of output locations specified by the user.
        basename (str): The base name of the file.
        language (str): The programming language.
        file_extension (str): The file extension, including the leading dot.
    
    Returns:
        dict: A dictionary where keys are output location types (e.g., 'output', 'output_test')
              and values are the corresponding full output paths.
    """
    output_paths = {}
    
    # Ensure all possible output keys are present, even if not specified by the user
    if command == 'fix':
        output_locations.setdefault('output_test', None)
        output_locations.setdefault('output_code', None)
        output_locations.setdefault('output_results', None)
    elif command == 'split':
        output_locations.setdefault('output_sub', None)
        output_locations.setdefault('output_modified', None)
    elif command == 'crash':
        output_locations.setdefault('output', None)
        output_locations.setdefault('output_program', None)
    else:
        output_locations.setdefault('output', None)
    
    for output_key, output_location in output_locations.items():
        if output_location:
            # User-specified output location
            if os.path.isabs(output_location) or os.path.isdir(output_location):
                # Absolute path or directory
                output_paths[output_key] = output_location
            else:
                # Filename only
                output_paths[output_key] = output_location
        else:
            # Check for environment variable override
            env_var_name = f"PDD_{command.upper()}"
            if output_key != 'output':
                env_var_name += f"_{output_key.upper()}"
            env_var_name += "_OUTPUT_PATH"
            
            env_var_value = os.environ.get(env_var_name)
            
            if env_var_value:
                # Environment variable is set
                if command == "detect":
                    default_filename = f"{basename}_detect.csv"
                elif command == "conflicts":
                    # Assuming prompt1 and prompt2 are available in this scope
                    # You might need to adjust this based on your actual implementation
                    prompt1_basename = os.path.splitext(os.path.basename(output_locations.get("prompt1", "")))[0]
                    prompt2_basename = os.path.splitext(os.path.basename(output_locations.get("prompt2", "")))[0]
                    default_filename = f"{prompt1_basename}_{prompt2_basename}_conflict.csv"
                else:
                    default_filename = get_default_filename(command, output_key, basename, language, file_extension)
                output_paths[output_key] = os.path.join(env_var_value, default_filename)
            else:
                # Use default naming convention
                default_filename = get_default_filename(command, output_key, basename, language, file_extension)
                output_paths[output_key] = default_filename
    
    return output_paths

def get_default_filename(command, output_key, basename, language, file_extension):
    """
    Generates a default filename based on the command and output key.
    
    Args:
        command (str): The command being executed.
        output_key (str): The output key (e.g., 'output', 'output_test').
        basename (str): The base name of the file.
        language (str): The programming language.
        file_extension (str): The file extension, including the leading dot.
    
    Returns:
        str: The default filename.
    """
    if command == "generate":
        return f"{basename}{file_extension}"
    elif command == "example":
        return f"{basename}_example{file_extension}"
    elif command == "test":
        return f"test_{basename}{file_extension}"
    elif command == "preprocess":
        return f"{basename}_{language}_preprocessed.prompt"
    elif command == "fix":
        if output_key == "output_test":
            return f"test_{basename}_fixed{file_extension}"
        elif output_key == "output_code":
            return f"{basename}_fixed{file_extension}"
        elif output_key == "output_results":
            return f"{basename}_fix_results.log"
    elif command == "split":
        if output_key == "output_sub":
            return f"sub_{basename}.prompt"
        elif output_key == "output_modified":
            return f"modified_{basename}.prompt"
    elif command == "change":
        return f"modified_{basename}.prompt"
    elif command == "update":
        return f"modified_{basename}.prompt"
    elif command == "detect":
        return f"{basename}_detect.csv"
    elif command == "conflicts":
        # Assuming prompt1 and prompt2 are available in this scope
        # You might need to adjust this based on your actual implementation
        prompt1_basename = os.path.splitext(os.path.basename(output_locations.get("prompt1", "")))[0]
        prompt2_basename = os.path.splitext(os.path.basename(output_locations.get("prompt2", "")))[0]
        return f"{prompt1_basename}_{prompt2_basename}_conflict.csv"
    elif command == "crash":
        if output_key == "output":
            return f"{basename}_fixed{file_extension}"
        elif output_key == "output_program":
            program_basename = os.path.splitext(basename)[0]  # Assuming program file has same basename
            return f"{program_basename}_fixed{file_extension}"
    elif command == "trace":
        return f"{basename}_trace_results.log"
    elif command == "bug":
        return f"test_{basename}_bug{file_extension}"
    elif command == "auto-deps":
        return f"{basename}_with_deps.prompt"
    else:
        raise ValueError(f"Unknown command: {command}")
