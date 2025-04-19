import os
import sys
from typing import Dict, Optional

# --- Assume the module code is in a file named 'output_path_generator.py'
# --- located one directory level up from the example script.
# --- Adjust the path manipulation if the structure is different.
# --- This handles the prompt's requirement about the example being in a different directory.
# Get the directory of the current script
current_dir = os.path.dirname(os.path.abspath(__file__))
# Get the parent directory (where the module is assumed to be)
parent_dir = os.path.dirname(current_dir)
# Add the parent directory to the Python path
sys.path.insert(0, parent_dir)

# Now import the function from the module
try:
    # Assuming the module file is named based on the function as per the prompt's context
    from pdd.generate_output_paths import generate_output_paths
except ImportError:
    print("Error: Could not import 'generate_output_paths'. "
          "Ensure 'generate_output_paths.py' exists in the parent directory "
          f"({parent_dir}) or is in the PYTHONPATH.")
    sys.exit(1)

# --- Example Usage ---

print("Demonstrating the use of generate_output_paths function.")

# Common inputs for examples
mock_basename = "my_code_module"
mock_language = "python"
mock_extension = ".py" # Note: the function handles adding '.' if missing

# Get current working directory for verifying absolute paths
cwd = os.getcwd()

# --- Scenario 1: Using Defaults ---
# No user input (--output options) and no relevant environment variables set.
print("\n--- Scenario 1: Defaults (generate command) ---")
output_locations_1: Dict[str, Optional[str]] = {}
paths_1 = generate_output_paths(
    command='generate',
    output_locations=output_locations_1,
    basename=mock_basename,
    language=mock_language,
    file_extension=mock_extension
)
print(f"Inputs: command='generate', output_locations={output_locations_1}, "
      f"basename='{mock_basename}', language='{mock_language}', extension='{mock_extension}'")
print(f"Result: {paths_1}")
# Expected: Default filename '{basename}{ext}' in the current working directory.
expected_path_1 = os.path.abspath(f"{mock_basename}{mock_extension}")
print(f"Expected: {{'output': '{expected_path_1}'}}")


# --- Scenario 2: User Specifies an Output Filename ---
# User provides '--output specific_name.py'
print("\n--- Scenario 2: User Filename (generate command) ---")
user_filename = "specific_output_name.py"
output_locations_2 = {'output': user_filename}
paths_2 = generate_output_paths(
    command='generate',
    output_locations=output_locations_2,
    basename=mock_basename,
    language=mock_language,
    file_extension=mock_extension
)
print(f"Inputs: command='generate', output_locations={output_locations_2}, ...")
print(f"Result: {paths_2}")
# Expected: The user-specified filename, resolved to an absolute path in CWD.
expected_path_2 = os.path.abspath(user_filename)
print(f"Expected: {{'output': '{expected_path_2}'}}")


# --- Scenario 3: User Specifies an Output Directory ---
# User provides '--output ./generated_files/'
print("\n--- Scenario 3: User Directory (generate command) ---")
user_dirname = "generated_files"
user_dir_path = user_dirname + os.path.sep # Indicate directory
# Create the directory for the example to work
os.makedirs(user_dirname, exist_ok=True)

output_locations_3 = {'output': user_dir_path}
paths_3 = generate_output_paths(
    command='generate',
    output_locations=output_locations_3,
    basename=mock_basename,
    language=mock_language,
    file_extension=mock_extension
)
print(f"Inputs: command='generate', output_locations={output_locations_3}, ...")
print(f"Result: {paths_3}")
# Expected: Default filename '{basename}{ext}' inside the user-specified directory.
default_filename_gen = f"{mock_basename}{mock_extension}"
expected_path_3 = os.path.abspath(os.path.join(user_dirname, default_filename_gen))
print(f"Expected: {{'output': '{expected_path_3}'}}")
# Clean up the created directory
os.rmdir(user_dirname)


# --- Scenario 4: Using Environment Variables ---
# No user input, but environment variables are set for the 'fix' command.
print("\n--- Scenario 4: Environment Variables (fix command) ---")
# Temporarily set environment variables for the example
env_var_code_key = 'PDD_FIX_CODE_OUTPUT_PATH'
env_var_results_key = 'PDD_FIX_RESULTS_OUTPUT_PATH'
env_code_path = os.path.join("env_output", "fixed_code_from_env.py")
env_results_dir = "env_results_logs" + os.path.sep

# Create directories needed for env var paths
os.makedirs(os.path.dirname(env_code_path), exist_ok=True)
os.makedirs(os.path.dirname(env_results_dir), exist_ok=True)

original_env_code = os.environ.get(env_var_code_key)
original_env_results = os.environ.get(env_var_results_key)
os.environ[env_var_code_key] = env_code_path      # Set as specific file
os.environ[env_var_results_key] = env_results_dir # Set as directory

output_locations_4: Dict[str, Optional[str]] = {} # No user overrides
paths_4 = generate_output_paths(
    command='fix',
    output_locations=output_locations_4,
    basename=mock_basename,
    language=mock_language,
    file_extension=mock_extension
)
print(f"Inputs: command='fix', output_locations={output_locations_4}, ...")
print(f"Env Vars: {env_var_code_key}='{env_code_path}', {env_var_results_key}='{env_results_dir}'")
print(f"Result: {paths_4}")

# Expected:
# - output_test: Default ('test_{basename}_fixed{ext}' in CWD)
# - output_code: From environment variable (specific file path)
# - output_results: Default filename ('{basename}_fix_results.log') inside env var directory
expected_path_test_def = os.path.abspath(f"test_{mock_basename}_fixed{mock_extension}")
expected_path_code_env = os.path.abspath(env_code_path)
default_filename_results = f"{mock_basename}_fix_results.log"
expected_path_results_env = os.path.abspath(os.path.join(env_results_dir, default_filename_results))

print(f"Expected: {{'output_test': '{expected_path_test_def}', "
      f"'output_code': '{expected_path_code_env}', "
      f"'output_results': '{expected_path_results_env}'}}")

# Clean up environment variables and directories
if original_env_code is None:
    del os.environ[env_var_code_key]
else:
    os.environ[env_var_code_key] = original_env_code
if original_env_results is None:
    del os.environ[env_var_results_key]
else:
    os.environ[env_var_results_key] = original_env_results

# Attempt to remove directories (will fail if not empty, which is fine for example)
try:
    os.rmdir(os.path.dirname(env_code_path))
    os.rmdir(os.path.dirname(env_results_dir))
except OSError:
    pass # Ignore errors if directories are not empty or already removed


# --- Scenario 5: Mixed User Input and Defaults (fix command) ---
# User specifies output_test (as dir) and output_code (as file), output_results uses default.
print("\n--- Scenario 5: Mixed Inputs (fix command) ---")
user_test_dir = "user_test_output" + os.path.sep
user_code_file = os.path.join("user_code_output", "my_fixed_module.py")

# Create directories needed
os.makedirs(os.path.dirname(user_test_dir), exist_ok=True)
os.makedirs(os.path.dirname(user_code_file), exist_ok=True)

output_locations_5 = {
    'output_test': user_test_dir,   # User specifies directory
    'output_code': user_code_file,  # User specifies file
    'output_results': None          # User does not specify, use default/env
}
paths_5 = generate_output_paths(
    command='fix',
    output_locations=output_locations_5,
    basename=mock_basename,
    language=mock_language,
    file_extension=mock_extension
)
print(f"Inputs: command='fix', output_locations={output_locations_5}, ...")
print(f"Result: {paths_5}")

# Expected:
# - output_test: Default filename in user-specified directory
# - output_code: User-specified filename
# - output_results: Default filename in CWD (assuming no env var)
default_filename_test = f"test_{mock_basename}_fixed{mock_extension}"
expected_path_test_user = os.path.abspath(os.path.join(user_test_dir, default_filename_test))
expected_path_code_user = os.path.abspath(user_code_file)
expected_path_results_def = os.path.abspath(f"{mock_basename}_fix_results.log")

print(f"Expected: {{'output_test': '{expected_path_test_user}', "
      f"'output_code': '{expected_path_code_user}', "
      f"'output_results': '{expected_path_results_def}'}}")

# Clean up created directories
try:
    os.rmdir(os.path.dirname(user_test_dir))
    os.rmdir(os.path.dirname(user_code_file))
except OSError:
    pass


# --- Scenario 6: Command with Fixed Extension Default ---
# 'preprocess' command default filename includes '.prompt', ignoring file_extension input.
print("\n--- Scenario 6: Fixed Extension Default (preprocess) ---")
output_locations_6: Dict[str, Optional[str]] = {}
paths_6 = generate_output_paths(
    command='preprocess',
    output_locations=output_locations_6,
    basename=mock_basename,
    language=mock_language,
    file_extension=".different_ext" # This should be ignored for the default
)
print(f"Inputs: command='preprocess', output_locations={output_locations_6}, "
      f"basename='{mock_basename}', language='{mock_language}', extension='.different_ext'")
print(f"Result: {paths_6}")
# Expected: Default filename '{basename}_{language}_preprocessed.prompt' in CWD.
expected_path_6 = os.path.abspath(f"{mock_basename}_{mock_language}_preprocessed.prompt")
print(f"Expected: {{'output': '{expected_path_6}'}}")


# --- Scenario 7: Unknown Command ---
# Providing a command not defined in COMMAND_OUTPUT_KEYS.
print("\n--- Scenario 7: Unknown Command ---")
output_locations_7: Dict[str, Optional[str]] = {}
paths_7 = generate_output_paths(
    command='invent', # This command is not configured
    output_locations=output_locations_7,
    basename=mock_basename,
    language=mock_language,
    file_extension=mock_extension
)
print(f"Inputs: command='invent', output_locations={output_locations_7}, ...")
print(f"Result: {paths_7}")
# Expected: An empty dictionary because the command is unknown.
print(f"Expected: {{}}")

# --- Scenario 8: No Basename Provided ---
# Basename is required for generating default filenames.
print("\n--- Scenario 8: No Basename Provided ---")
output_locations_8: Dict[str, Optional[str]] = {}
paths_8 = generate_output_paths(
    command='generate',
    output_locations=output_locations_8,
    basename="", # Empty basename
    language=mock_language,
    file_extension=mock_extension
)
print(f"Inputs: command='generate', output_locations={output_locations_8}, basename='', ...")
print(f"Result: {paths_8}")
# Expected: An empty dictionary because basename is missing.
print(f"Expected: {{}}")
