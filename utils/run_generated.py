import sys
import os
import importlib.util

def run_generated(prompt_file_path: str) -> None:
    """
    Executes a generated Python script based on the provided prompt file path.

    :param prompt_file_path: Path to the prompt file used to generate the script.
    """
    # Check if the prompt file exists
    if not os.path.exists(prompt_file_path):
        print(f"Error: Prompt file '{prompt_file_path}' does not exist.")
        return

    # Extract the base filename without the '_python.prompt' suffix
    base_filename = os.path.basename(prompt_file_path)
    if not base_filename.endswith('_python.prompt'):
        print(f"Error: Invalid prompt file name. Expected '_python.prompt' suffix.")
        return
    base_filename = base_filename[:-14]  # Remove '_python.prompt'

    # Construct the path for the generated Python script
    script_directory = os.path.dirname(prompt_file_path).replace('prompts', 'pdd')
    script_path = os.path.join(script_directory, f"{base_filename}.py")

    # Check if the generated Python script exists
    if not os.path.exists(script_path):
        print(f"Error: Generated Python script '{script_path}' does not exist.")
        return

    try:
        # Load the module dynamically
        spec = importlib.util.spec_from_file_location("generated_script", script_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        print(f"Successfully executed the generated Python script: {script_path}")
    except Exception as e:
        print(f"Error occurred while executing the script: {str(e)}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python run_generated.py <prompt_file_path>")
    else:
        prompt_file_path = sys.argv[1]
        run_generated(prompt_file_path)
