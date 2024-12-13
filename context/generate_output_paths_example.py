import os
from pathlib import Path
from pdd.generate_output_paths import generate_output_paths

# Set up example inputs
command = "generate"
output_locations = {"output": "/path/to/output/"}
basename = "my_project"
language = "python"
file_extension = ".py"

# Generate output paths
result = generate_output_paths(command, output_locations, basename, language, file_extension)

# Print the result
print(f"Generated output path: {result['output']}")

# Example with environment variable
os.environ["PDD_GENERATE_OUTPUT_PATH"] = "./tmp"
result_with_env = generate_output_paths(command, {}, basename, language, file_extension)
print(f"Generated output path with env variable: {result_with_env['output']}")

# Example for 'fix' command with multiple outputs
fix_command = "fix"
fix_output_locations = {
    "output_test": "./fix/test.py",
    "output_code": "./fix/code.py"
}
fix_result = generate_output_paths(fix_command, fix_output_locations, basename, language, file_extension)
print(f"Generated test output path: {fix_result['output_test']}")
print(f"Generated code output path: {fix_result['output_code']}")
print(f"Generated results output path: {fix_result['output_results']}")