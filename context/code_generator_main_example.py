import click
import os
import pathlib
import shutil
from unittest.mock import patch

# Assuming 'pdd' package is installed and pdd.code_generator_main is accessible.
# If pdd.code_generator_main is the name of the file, and it's in a 'pdd' directory
# that is in PYTHONPATH or installed.
from pdd.code_generator_main import code_generator_main 

# --- Mocked constants (normally from pdd.__init__) ---
# These are needed because code_generator_main uses them as defaults
# or for its logic, and the example script is standalone.
DEFAULT_STRENGTH = 0.5
DEFAULT_TIME = 0.25
EXTRACTION_STRENGTH = 0.7 # Example value
FIREBASE_API_KEY_ENV_VAR = "NEXT_PUBLIC_FIREBASE_API_KEY" 
GITHUB_CLIENT_ID_ENV_VAR = "GITHUB_CLIENT_ID"

# --- Mocked internal generator functions ---
# These prevent actual LLM calls, making the example self-contained,
# predictable, and fast, without requiring real API keys to run.
def mock_local_code_generator_func(prompt: str, language: str, strength: float, temperature: float, verbose: bool):
    """Mocks the local_code_generator function."""
    if verbose:
        print(f"[Mock] Called local_code_generator_func for lang '{language}' with prompt: '{prompt[:30]}...'")
    generated_code = f"// Mock local code for: {language}\n"
    generated_code += f"// Prompt: {prompt[:70]}...\n"
    generated_code += f"// Strength: {strength}, Temp: {temperature}\n"
    generated_code += "public class Main { public static void main(String[] args) { System.out.println(\"Hello from Mock Local!\"); } }"
    return generated_code, 0.001, "mock_local_model_v1"

def mock_incremental_code_generator_func(original_prompt: str, new_prompt: str, existing_code: str, language: str, strength: float, temperature: float, time: float, force_incremental: bool, verbose: bool, preprocess_prompt: bool):
    """Mocks the incremental_code_generator function."""
    if verbose:
        print(f"[Mock] Called incremental_code_generator_func for lang '{language}' with new_prompt: '{new_prompt[:30]}...'")
    
    # Simulate a scenario where incremental generation decides full regeneration is better
    if "very_significant_change" in new_prompt and not force_incremental:
        if verbose:
            print("[Mock] Incremental decided full regeneration is better for this change.")
        return existing_code, False, 0.0005, "mock_inc_model_suggests_full"

    updated_code = f"// Mock incrementally updated code for: {language}\n"
    updated_code += f"// Original Prompt Hint: {original_prompt[:50]}...\n"
    updated_code += f"// New Prompt Hint: {new_prompt[:50]}...\n"
    updated_code += f"// --- Appended to existing code ---\n{existing_code}\n"
    updated_code += "// Change: Added a new comment and method.\n"
    updated_code += "public void newMethod() { System.out.println(\"New method from incremental update!\"); }"
    return updated_code, True, 0.002, "mock_inc_model_v1_diff"

class MockContext:
    """A simple mock for click.Context."""
    def __init__(self, params: dict):
        self.obj = params if params is not None else {}

def print_generation_results(scenario_name: str, code: str, incremental: bool, cost: float, model: str, output_file: pathlib.Path = None):
    """Helper to print results."""
    print(f"\n--- Results for {scenario_name} ---")
    print(f"Generated/Updated Code (first 150 chars): \n{code[:150]}...")
    if output_file and output_file.exists():
        print(f"Full content in: {output_file.resolve()}")
    elif output_file:
        print(f"Output file {output_file.resolve()} was NOT created (as expected if no output path or error).")
    print(f"Was Incremental: {incremental}")
    print(f"Total Cost: ${cost:.6f}")
    print(f"Model Name: {model}")
    print("--------------------------------------")

def main_example():
    """
    Demonstrates how to use the code_generator_main function from the PDD CLI.
    This example covers:
    1. Full code generation with local execution.
    2. Incremental code generation (using explicit original prompt) with local execution.
    3. Forced incremental code generation.
    4. Attempted cloud code generation (which will fall back to local due to mocked auth/network).
    
    It uses mocked versions of the actual code generator functions (local_code_generator_func
    and incremental_code_generator_func) to avoid real LLM calls and API key requirements,
    making the example self-contained and predictable.
    """
    base_output_dir = pathlib.Path("./output/code_generator_main_example_output")
    # Clean up previous run's output
    if base_output_dir.exists():
        shutil.rmtree(base_output_dir)
    base_output_dir.mkdir(parents=True, exist_ok=True)

    # --- Scenario 1: Full code generation (local execution) ---
    scenario1_name = "Scenario 1: Full Generation (Local)"
    print(f"\nRunning {scenario1_name}...")
    s1_prompt_content = "Create a simple Java program that prints 'Hello, World!'."
    s1_prompt_file = base_output_dir / "s1_hello_java.prompt"
    s1_prompt_file.write_text(s1_prompt_content)
    s1_output_file = base_output_dir / "s1_HelloWorld.java"

    s1_cli_params = {
        'local': True, 'strength': DEFAULT_STRENGTH, 'temperature': 0.1, 
        'time': DEFAULT_TIME, 'verbose': True, 'force': False, 'quiet': False
    }
    s1_ctx = MockContext(s1_cli_params)

    code, incremental, cost, model = code_generator_main(
        ctx=s1_ctx,
        prompt_file=str(s1_prompt_file),
        output=str(s1_output_file),
        original_prompt_file_path=None,
        force_incremental_flag=False
    )
    print_generation_results(scenario1_name, code, incremental, cost, model, s1_output_file)

    # --- Scenario 2: Incremental code generation (explicit original prompt, local) ---
    scenario2_name = "Scenario 2: Incremental Generation (Explicit Original, Local)"
    print(f"\nRunning {scenario2_name}...")
    s2_original_prompt_content = "Create a basic Python function `greet()` that returns 'Hello'."
    s2_new_prompt_content = "Modify the Python function `greet()` to accept a name and return 'Hello, [name]!'."
    s2_existing_code_content = "def greet():\n    return \"Hello\""
    
    s2_original_prompt_file = base_output_dir / "s2_original_greet_python.prompt"
    s2_new_prompt_file = base_output_dir / "s2_new_greet_python.prompt"
    s2_output_code_file = base_output_dir / "s2_greet.py"

    s2_original_prompt_file.write_text(s2_original_prompt_content)
    s2_new_prompt_file.write_text(s2_new_prompt_content)
    s2_output_code_file.write_text(s2_existing_code_content)

    s2_cli_params = {
        'local': True, 'strength': 0.6, 'temperature': 0.2, 
        'time': 0.3, 'verbose': True, 'force': False, 'quiet': False
    }
    s2_ctx = MockContext(s2_cli_params)

    code, incremental, cost, model = code_generator_main(
        ctx=s2_ctx,
        prompt_file=str(s2_new_prompt_file),
        output=str(s2_output_code_file),
        original_prompt_file_path=str(s2_original_prompt_file),
        force_incremental_flag=False
    )
    print_generation_results(scenario2_name, code, incremental, cost, model, s2_output_code_file)

    # --- Scenario 2b: Forced Incremental (even if model suggests full) ---
    scenario2b_name = "Scenario 2b: Forced Incremental Generation"
    print(f"\nRunning {scenario2b_name}...")
    # Use a prompt that the mock would normally suggest full regen for
    s2b_new_prompt_content = "very_significant_change: Rewrite the Python function `greet()` entirely to be a class `Greeter`."
    s2_new_prompt_file.write_text(s2b_new_prompt_content) # Overwrite s2_new_prompt_file for this sub-scenario

    # s2_output_code_file already exists with content from previous step
    
    code, incremental, cost, model = code_generator_main(
        ctx=s2_ctx, # Re-use context from s2
        prompt_file=str(s2_new_prompt_file),
        output=str(s2_output_code_file),
        original_prompt_file_path=str(s2_original_prompt_file),
        force_incremental_flag=True # Force incremental
    )
    print_generation_results(scenario2b_name, code, incremental, cost, model, s2_output_code_file)


    # --- Scenario 3: Cloud generation attempt (will fallback to local) ---
    scenario3_name = "Scenario 3: Cloud Generation Attempt (Fallback to Local)"
    print(f"\nRunning {scenario3_name}...")
    # Set dummy env vars required for cloud auth attempt
    os.environ[FIREBASE_API_KEY_ENV_VAR] = "dummy_firebase_api_key"
    os.environ[GITHUB_CLIENT_ID_ENV_VAR] = "dummy_github_client_id"

    s3_prompt_content = "Generate a C# snippet to read a file."
    s3_prompt_file = base_output_dir / "s3_readfile_csharp.prompt"
    s3_prompt_file.write_text(s3_prompt_content)
    s3_output_file = base_output_dir / "s3_FileReader.cs"

    s3_cli_params = {
        'local': False, # Attempt cloud
        'strength': 0.7, 'temperature': 0.3, 
        'time': 0.4, 'verbose': True, 'force': False, 'quiet': False
    }
    s3_ctx = MockContext(s3_cli_params)
    
    # Note: The actual cloud call will likely fail due to dummy keys or network isolation
    # and the function is designed to fall back to local execution.
    # Our mock_local_code_generator_func will then be hit.
    code, incremental, cost, model = code_generator_main(
        ctx=s3_ctx,
        prompt_file=str(s3_prompt_file),
        output=str(s3_output_file),
        original_prompt_file_path=None,
        force_incremental_flag=False
    )
    print_generation_results(scenario3_name, code, incremental, cost, model, s3_output_file)

    # Clean up dummy env vars
    del os.environ[FIREBASE_API_KEY_ENV_VAR]
    del os.environ[GITHUB_CLIENT_ID_ENV_VAR]

    print("\nExample execution finished. Check the './output/code_generator_main_example_output' directory.")

if __name__ == "__main__":
    # Apply patches globally for the main_example execution.
    # This ensures that the code_generator_main function, when it internally calls
    # local_code_generator_func or incremental_code_generator_func, will use our mocks.
    # The paths to patch are relative to where code_generator_main *thinks* these functions are.
    # If code_generator_main.py has "from .code_generator import code_generator as local_code_generator_func",
    # then the path to patch is 'pdd.code_generator_main.local_code_generator_func'.
    with patch('pdd.code_generator_main.local_code_generator_func', new=mock_local_code_generator_func), \
         patch('pdd.code_generator_main.incremental_code_generator_func', new=mock_incremental_code_generator_func):
        main_example()
