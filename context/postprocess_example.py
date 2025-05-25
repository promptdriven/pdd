"""
Example demonstrating the usage of the `postprocess` function 
from the `pdd.postprocess` module.

This example showcases two scenarios for extracting code from an LLM's text output:
1. Simple code extraction (strength = 0): Uses basic string manipulation to find code
   blocks enclosed in triple backticks. This method is fast and has no cost.
2. Advanced code extraction (strength > 0): Leverages an LLM for more robust extraction.
   This method is more powerful but incurs a cost and takes more time.

To run this example:
1. Ensure the `pdd` package (containing the `postprocess` module) is in your PYTHONPATH
   or installed in your environment.
2. Ensure the `rich` library is installed (`pip install rich`).
3. This script uses `unittest.mock` (part of Python's standard library) to simulate
   the behavior of internal dependencies (`load_prompt_template` and `llm_invoke`)
   for the LLM-based extraction scenario. This allows the example to run without
   requiring actual LLM API calls or specific prompt files.
"""
from rich import print
from unittest.mock import patch, MagicMock

# Assuming 'pdd' package is in PYTHONPATH or installed.
# The 'postprocess' module is expected to be at pdd/postprocess.py
from pdd.postprocess import postprocess, ExtractedCode # ExtractedCode is needed for the mock

def main():
    """
    Runs the demonstration for the postprocess function.
    """
    print("[bold underline blue]Demonstrating `postprocess` function from `pdd.postprocess`[/bold underline blue]\n")

    # --- Common Inputs ---
    # This is a sample string that might be output by an LLM, containing text and code.
    llm_output_text_with_code = """
This is some text from an LLM.
It includes a Python code block:
```python
def greet(name):
    # A simple greeting function
    print(f"Hello, {name}!")

greet("Developer")
```
And some more text after the code block.
There might be other language blocks too:
```javascript
console.log("This is JavaScript");
```
But we are only interested in Python.
"""
    # The target programming language for extraction.
    target_language = "python"

    # --- Scenario 1: Simple Extraction (strength = 0) ---
    # This mode uses the `postprocess_0` internal function, which performs a basic
    # extraction of content between triple backticks. It does not use an LLM.
    print("[bold cyan]Scenario 1: Simple Extraction (strength = 0)[/bold cyan]")
    print("Demonstrates extracting code using basic string processing.")
    print(f"  Input LLM Output: (see below)")
    # print(f"[dim]{llm_output_text_with_code}[/dim]") # Printing for brevity in console
    print(f"  Target Language: '{target_language}' (Note: simple extraction is language-agnostic but extracts first block)")
    print(f"  Strength: 0 (activates simple, non-LLM extraction)")
    print(f"  Verbose: True (enables detailed console output from `postprocess`)\n")

    # Call postprocess with strength = 0
    # Input parameters:
    #   llm_output (str): The LLM's raw output string.
    #   language (str): The programming language to extract (less critical for strength=0).
    #   strength (float): 0-1, model strength. 0 means simple extraction.
    #   temperature (float): 0-1, LLM temperature (not used for strength=0).
    #   time (float): 0-1, LLM thinking effort (not used for strength=0).
    #   verbose (bool): If True, prints internal processing steps.
    extracted_code_s0, cost_s0, model_s0 = postprocess(
        llm_output=llm_output_text_with_code,
        language=target_language,
        strength=0,
        verbose=True
    )

    print("[bold green]Output for Scenario 1:[/bold green]")
    # Output tuple:
    #   extracted_code (str): The extracted code.
    #   total_cost (float): Cost of the operation (in dollars). Expected to be 0.0 for simple extraction.
    #   model_name (str): Identifier for the method/model used. Expected to be 'simple_extraction'.
    print(f"  Extracted Code:\n[yellow]{extracted_code_s0}[/yellow]")
    print(f"  Total Cost: ${cost_s0:.6f}")
    print(f"  Model Name: '{model_s0}'")
    print("-" * 60)

    # --- Scenario 2: LLM-based Extraction (strength > 0) ---
    # This mode uses an LLM via `llm_invoke` to perform a more sophisticated extraction.
    # It requires a prompt template (`extract_code_LLM.prompt`).
    # For this example, `load_prompt_template` and `llm_invoke` are mocked.
    print("\n[bold cyan]Scenario 2: LLM-based Extraction (strength = 0.9)[/bold cyan]")
    print("Demonstrates extracting code using an LLM (mocked).")
    print(f"  Input LLM Output: (same as above)")
    print(f"  Target Language: '{target_language}'")
    print(f"  Strength: 0.9 (activates LLM-based extraction)")
    print(f"  Temperature: 0.0 (LLM creativity, 0-1 scale)")
    print(f"  Time: 0.5 (LLM thinking effort, 0-1 scale, influences model choice/cost)")
    print(f"  Verbose: True\n")

    # Mock for `load_prompt_template`:
    # This function is expected to load a prompt template file (e.g., 'extract_code_LLM.prompt').
    # In a real scenario, this file would exist in a 'prompts' directory.
    mock_load_template = MagicMock(return_value="Mocked Prompt: Extract {{language}} code from: {{llm_output}}")

    # Mock for `llm_invoke`:
    # This function handles the actual LLM API call.
    # It's expected to return a dictionary containing the LLM's result (parsed into
    # an `ExtractedCode` Pydantic model), the cost, and the model name.
    # The `extracted_code` from the LLM mock should include backticks and language identifier
    # to test the cleaning step within the `postprocess` function.
    mock_llm_response_code_from_llm = """```python
def sophisticated_extraction(data):
    # This code is supposedly extracted by an LLM
    processed_data = data.upper()  # Example processing
    return processed_data

result = sophisticated_extraction("test data from llm")
print(result)
```"""
    mock_extracted_code_pydantic_obj = ExtractedCode(extracted_code=mock_llm_response_code_from_llm)
    mock_llm_invoke_return_value = {
        'result': mock_extracted_code_pydantic_obj,
        'cost': 0.00025,  # Example cost in dollars
        'model_name': 'mock-llm-extractor-v1'
    }
    mock_llm_invoke_function = MagicMock(return_value=mock_llm_invoke_return_value)

    # Patch the internal dependencies within the 'pdd.postprocess' module's namespace.
    # This ensures that when `postprocess` calls `load_prompt_template` or `llm_invoke`,
    # our mocks are used instead of the real implementations.
    with patch('pdd.postprocess.load_prompt_template', mock_load_template):
        with patch('pdd.postprocess.llm_invoke', mock_llm_invoke_function):
            extracted_code_llm, cost_llm, model_llm = postprocess(
                llm_output=llm_output_text_with_code,
                language=target_language,
                strength=0.9,
                temperature=0.0,
                time=0.5,
                verbose=True
            )

            print("[bold green]Output for Scenario 2:[/bold green]")
            print(f"  Extracted Code:\n[yellow]{extracted_code_llm}[/yellow]")
            print(f"  Total Cost: ${cost_llm:.6f} (cost is in dollars)")
            print(f"  Model Name: '{model_llm}'")

            # --- Verification of Mock Calls (for developer understanding) ---
            # Check that `load_prompt_template` was called correctly.
            mock_load_template.assert_called_once_with("extract_code_LLM")

            # Check that `llm_invoke` was called correctly.
            mock_llm_invoke_function.assert_called_once()
            # Inspect the arguments passed to the mocked llm_invoke
            call_args_to_llm_invoke = mock_llm_invoke_function.call_args[1] # kwargs
            assert call_args_to_llm_invoke['prompt'] == mock_load_template.return_value
            assert call_args_to_llm_invoke['input_json'] == {
                "llm_output": llm_output_text_with_code,
                "language": target_language
            }
            assert call_args_to_llm_invoke['strength'] == 0.9
            assert call_args_to_llm_invoke['temperature'] == 0.0
            assert call_args_to_llm_invoke['time'] == 0.5
            assert call_args_to_llm_invoke['verbose'] is True
            assert call_args_to_llm_invoke['output_pydantic'] == ExtractedCode
            print("[dim]  (Mocked LLM calls verified successfully)[/dim]")

    print("\n[bold underline blue]Demonstration finished.[/bold underline blue]")
    print("\n[italic]Important Notes:[/italic]")
    print("  - For Scenario 2 (LLM-based extraction), `load_prompt_template` and `llm_invoke` were mocked.")
    print("    In a real-world scenario:")
    print("    - `load_prompt_template('extract_code_LLM')` would attempt to load a file named ")
    print("      `extract_code_LLM.prompt` (typically from a 'prompts' directory configured within the `pdd` package).")
    print("    - `llm_invoke` would make an actual API call to a Large Language Model, which requires")
    print("      API keys and network access.")
    print("  - The `time` parameter (0-1) for `postprocess` (and `llm_invoke`) generally controls the")
    print("    'thinking effort' or computational resources allocated to the LLM, potentially affecting")
    print("    which underlying LLM model is chosen and the quality/cost of the result.")
    print("  - No actual files (like prompt files or output files) are created or read by this example script,")
    print("    particularly in the './output' directory, due to the use of mocks for file-dependent operations.")

if __name__ == "__main__":
    main()
