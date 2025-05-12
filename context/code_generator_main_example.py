import click
from pathlib import Path
import os
import shutil # For cleaning up the created directory (optional)

# Assuming the 'pdd' package (containing code_generator_main.py and __init__.py)
# is in PYTHONPATH, installed, or PDD_PATH is set up correctly.
from pdd.code_generator_main import code_generator_main
from pdd import DEFAULT_STRENGTH # Default strength for model selection

# Helper to create a mock Click context, as code_generator_main expects it.
# In a real CLI application, Click would provide this context.
class MockContext:
    def __init__(self):
        self.obj = {}

def run_code_generation_example() -> None:
    """
    Demonstrates how to use the code_generator_main function.

    This function will:
    1. Create a dummy prompt file.
    2. Set up a mock Click context with necessary parameters.
    3. Call code_generator_main for full code generation in local mode.
    4. Print the results, including the generated code snippet, operation type, cost, and model name.

    Prerequisites for this example:
    - The 'pdd' package is accessible in the Python environment.
    - For local generation (as shown):
        - Underlying LLM API keys (e.g., OPENAI_API_KEY) might be required by the
          `pdd.code_generator.code_generator` function, depending on its implementation
          and the selected model. The example will run, but code generation might fail
          if keys are missing for the chosen local model.
    - For cloud generation (if `ctx.obj['local']` is set to `False`):
        - `REACT_APP_FIREBASE_API_KEY` and `GITHUB_CLIENT_ID` environment variables
          must be set for authentication.
    """
    example_output_dir: Path = Path("pdd_example_output")
    example_output_dir.mkdir(exist_ok=True)

    prompt_filename: str = "calculator_python.prompt"
    prompt_file_path: Path = example_output_dir / prompt_filename
    
    # The output path for the generated code.
    # construct_paths within code_generator_main will derive the actual filename (e.g., calculator.py)
    # if 'output' is a directory. Here, we specify a file.
    generated_code_path: Path = example_output_dir / "calculator.py"

    # 1. Create a dummy prompt file
    # The prompt file name convention (<basename>_<language>.prompt) helps determine the language.
    prompt_content: str = """
    # Task: Implement a simple calculator
    # Language: Python

    # Function: add
    # Description: Adds two integers.
    # Inputs: a (int), b (int)
    # Output: The sum of a and b (int).

    # Function: subtract
    # Description: Subtracts the second integer from the first.
    # Inputs: a (int), b (int)
    # Output: The difference (int).
    """
    prompt_file_path.write_text(prompt_content, encoding="utf-8")
    print(f"Created prompt file: {prompt_file_path}")

    # 2. Prepare Click context object
    # The code_generator_main function expects certain configuration values in ctx.obj.
    ctx = MockContext()
    ctx.obj['verbose'] = True       # Enables detailed logging from code_generator_main.
    ctx.obj['force'] = True         # Allows overwriting of output files.
    ctx.obj['strength'] = DEFAULT_STRENGTH  # Model selection strength (0.0 to 1.0).
                                        # DEFAULT_STRENGTH is imported from pdd.__init__.py.
    ctx.obj['temperature'] = 0.0    # LLM temperature (0.0 for deterministic output).
    ctx.obj['local'] = True         # True for local generation, False for cloud.
    ctx.obj['quiet'] = False        # Set to True to suppress most informational output.

    # 3. Define other parameters for code_generator_main
    output_path_str: str = str(generated_code_path)
    original_prompt_path_str: None = None # Not used for full generation.
    use_incremental_flag: bool = False    # False for full generation.
    llm_time_param: float = 0.25           # Reasoning effort/time for LLM (unitless, model-dependent).

    print(f"\nCalling code_generator_main for full generation (local mode)...")
    # Note: If this script is run in a directory that is not part of a Git repository,
    # Git-related operations within code_generator_main (like staging) will be skipped
    # or may print warnings, which is acceptable for this example focusing on generation.

    generated_code, is_incremental, cost, model_name = code_generator_main(
        ctx=ctx,
        prompt_file=str(prompt_file_path),
        output=output_path_str,
        original_prompt=original_prompt_path_str,
        incremental=use_incremental_flag,
        time=llm_time_param
    )

    # 4. Print the results
    print("\n--- code_generator_main Results ---")
    print(f"Generated Code (intended for {output_path_str}):")
    if generated_code:
        # Displaying a snippet of the generated code
        code_lines = generated_code.splitlines()
        for i, line in enumerate(code_lines):
            if i < 15:  # Print up to 15 lines
                print(f"  {line}")
            elif i == 15:
                print("  ...")
                break
        if not code_lines: # Handles empty string case
             print("  (No code was generated, or an error occurred during generation.)")
        if Path(output_path_str).exists():
            print(f"\n[Code has been saved to: {Path(output_path_str).resolve()}]")
        else:
            print(f"\n[Code was NOT saved to {output_path_str} (it might have been displayed to console by the module if no output path was resolved).]")

    else:
        print("  (No code was generated, or an error occurred during generation.)")

    print(f"Was Incremental Operation: {is_incremental}") # Expected: False for this example
    print(f"Total Cost: ${cost:.6f}") # Estimated cost in USD. Will be 0.0 if local model/no cost tracking.
    print(f"Model Name Used: {model_name if model_name else 'N/A'}")

    # To run in cloud mode (ensure REACT_APP_FIREBASE_API_KEY and GITHUB_CLIENT_ID env vars are set):
    # ctx.obj['local'] = False
    # print("\nAttempting cloud generation (example - commented out)...")
    # generated_code_cloud, is_inc_cloud, cost_cloud, model_cloud = code_generator_main(
    #     ctx=ctx, prompt_file=str(prompt_file_path), output=output_path_str,
    #     original_prompt=None, incremental=False, time=llm_time_param
    # )
    # print(f"Cloud - Incremental: {is_inc_cloud}, Cost: ${cost_cloud:.6f}, Model: {model_cloud}")


    # Optional: Clean up the created directory and its contents
    # try:
    #     shutil.rmtree(example_output_dir)
    #     print(f"\nCleaned up directory: {example_output_dir}")
    # except OSError as e:
    #     print(f"\nError cleaning up directory {example_output_dir}: {e}")

if __name__ == "__main__":
    run_code_generation_example()
