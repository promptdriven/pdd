"""
Example script demonstrating how to use the fix_verification_errors function
from the pdd package to automatically identify and fix errors in a code
module based on verification output logs.

Assumptions for this example to run:
- The 'pdd' package containing 'fix_verification_errors' is installed or accessible
  in the Python path (e.g., via PYTHONPATH or `pip install -e .`).
- Required prompt template files ('find_verification_errors_LLM.prompt',
  'fix_verification_errors_LLM.prompt') exist where the internal
  'load_prompt_template' function can find them (likely configured via an
  environment variable like PDD_PROMPT_TEMPLATE_DIR used by load_prompt_template).
- Necessary LLM API keys (e.g., OPENAI_API_KEY) are configured in the environment
  for the internal 'llm_invoke' function to use.
- The PDD_PATH environment variable is set correctly if required by internal modules.
"""

from rich import print
# Assuming 'pdd' package is installed or accessible in the Python path.
# This imports the function from the specified module within the package.
from pdd.fix_verification_errors import fix_verification_errors

# --- Define Example Inputs ---

# 1. program: String containing the Python script that uses the code module.
#    This script should ideally contain some form of verification logic
#    whose output can indicate success or failure.
program_code = """
import calculator_module # The code module to be verified/fixed
import sys

# Example: Get inputs from command line
if len(sys.argv) != 3:
    print("Usage: python program.py <num1> <num2>")
    sys.exit(1)

a = int(sys.argv[1])
b = int(sys.argv[2])

print(f"Running calculator_module.add_numbers({a}, {b})")
result = calculator_module.add_numbers(a, b)

# Verification logic embedded in the program
expected = a + b
print(f"Expected result: {expected}")
print(f"Actual result: {result}")

if result == expected:
    print("VERIFICATION_SUCCESS: Result matches expectation.")
else:
    # Provide a clear failure indicator for the LLM
    print("VERIFICATION_FAILURE: Result does not match expectation.")
    # In a real scenario, might exit or raise an error
    # sys.exit(1)
"""

# 2. prompt: String containing the original prompt used to generate the 'code' module.
#    This gives context to the LLM about the intended functionality.
original_prompt = "Create a Python module named 'calculator_module.py' containing a function `add_numbers(a: int, b: int) -> int` that returns the sum of the two integer inputs."

# 3. code: String containing the code module content (potentially with errors).
#    This version has an intentional bug (subtraction instead of addition).
buggy_code_module = """
# calculator_module.py
# Module generated based on a prompt.

def add_numbers(a: int, b: int) -> int:
    '''Calculates the sum of two integers.'''
    # Bug: Incorrectly implemented subtraction instead of addition
    result = a - b
    return result
"""

# 4. output: String containing the captured stdout/stderr from running the 'program'.
#    This output MUST contain clues for the LLM about success or failure.
#    Using clear markers like "VERIFICATION_SUCCESS" or "VERIFICATION_FAILURE" helps.
verification_output = """
Running calculator_module.add_numbers(10, 5)
Expected result: 15
Actual result: 5
VERIFICATION_FAILURE: Result does not match expectation.
"""

# 5. strength: Float (0.0 to 1.0) controlling LLM capability/model selection.
#    Higher values generally use more powerful (and potentially expensive) models.
llm_strength = 0.5 # Example: Use a mid-range model

# 6. temperature: Float (>= 0.0) controlling LLM randomness.
#    0.0 is deterministic, higher values increase creativity/variability.
llm_temperature = 0.0 # Example: Aim for deterministic fixes

# 7. verbose: Boolean flag to enable detailed logging from the function.
verbose_mode = True

# --- Execute the Function ---
print("[bold blue]Calling fix_verification_errors...[/bold blue]")
print("This function will use LLMs to:")
print("1. Analyze the verification output to find issues in the code module.")
print("2. If issues are found, attempt to fix the code module and potentially the program.")
print("-" * 30)

# Call the function with the prepared inputs
results = fix_verification_errors(
    program=program_code,
    prompt=original_prompt,
    code=buggy_code_module,
    output=verification_output,
    strength=llm_strength,
    temperature=llm_temperature,
    verbose=verbose_mode
)

# --- Display Results ---
print("-" + "=" * 40)
print("[bold green]fix_verification_errors Execution Results[/bold green]")
print("=" * 40)

# The function returns a dictionary containing the results.
# 'issues_found': Boolean - True if the first LLM call identified potential issues.
# 'update_program': Boolean - True if the LLM suggested changes to the program code.
# 'update_code': Boolean - True if the LLM suggested changes to the code module.
# 'fixed_program': String - The potentially modified program code.
# 'fixed_code': String - The potentially modified code module.
# 'total_cost': Float - Estimated cost of the LLM calls in dollars.
# 'model_name': String - Name of the LLM model used (can vary based on strength).

print(f"[cyan]Issues Found by LLM:[/cyan] {results['issues_found']}")
print(f"[cyan]Program Updated:[/cyan] {results['update_program']}")
print(f"[cyan]Code Module Updated:[/cyan] {results['update_code']}")
print(f"[cyan]LLM Model Used:[/cyan] {results['model_name']}")
print(f"[cyan]Total LLM Cost:[/cyan] ${results['total_cost']:.6f}") # Cost in dollars

print("\n[bold yellow]--- Details ---[/bold yellow]")

if results['update_program']:
    print("\n[bold magenta]--- Fixed Program ---[/bold magenta]")
    print(results['fixed_program'])
else:
    print("\n[bold magenta]--- Original Program (Unchanged) ---[/bold magenta]")
    # Optionally print the original program_code again if needed for comparison
    # print(program_code)

if results['update_code']:
    print("\n[bold magenta]--- Fixed Code Module ---[/bold magenta]")
    print(results['fixed_code'])
else:
    print("\n[bold magenta]--- Original Code Module (Unchanged) ---[/bold magenta]")
    # Optionally print the buggy_code_module again if needed for comparison
    # print(buggy_code_module)

print("\n[bold blue]Example finished.[/bold blue]")