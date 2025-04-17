# Import necessary modules
from pathlib import Path
from pdd.fix_verification_errors_loop import fix_verification_errors_loop

# --- Define Example Inputs ---

# 1. program_file: Path to the Python program that exercises the code_file.
program_file = Path("output/program.py")
program_code = """
import calculator_module  # The code module to be verified/fixed
import sys

if len(sys.argv) != 3:
    print("Usage: python program.py <num1> <num2>")
    sys.exit(1)

a = int(sys.argv[1])
b = int(sys.argv[2])

print(f"Running calculator_module.add_numbers({{a}}, {{b}})")
result = calculator_module.add_numbers(a, b)

expected = a + b
print(f"Expected result: {{expected}}")
print(f"Actual result: {{result}}")

if result == expected:
    print("VERIFICATION_SUCCESS: Result matches expectation.")
else:
    print("VERIFICATION_FAILURE: Result does not match expectation.")
"""

# Write the program code to a file
program_file.write_text(program_code)

# 2. code_file: Path to the code file being tested/verified.
code_file = Path("output/calculator_module.py")
buggy_code_module = """
def add_numbers(a: int, b: int) -> int:
    '''Calculates the sum of two integers.'''
    result = a - b  # Intentional bug: subtraction instead of addition
    return result
"""

# Write the buggy code to a file
code_file.write_text(buggy_code_module)

# 3. prompt: The original prompt used to generate the code.
prompt = "Create a Python module named 'calculator_module.py' containing a function `add_numbers(a: int, b: int) -> int` that returns the sum of the two integer inputs."

# 4. verification_program: Path to a secondary verification program.
verification_program = Path("output/verification_program.py")
verification_program_code = """
import calculator_module

def verify_code():
    # This function can perform basic checks on the calculator_module
    assert calculator_module.add_numbers(1, 2) == 3, "Test failed: 1 + 2 should equal 3"
    print("Verification passed.")

if __name__ == "__main__":
    verify_code()
"""

# Write the verification program code to a file
verification_program.write_text(verification_program_code)

# 5. strength: Float controlling LLM capability/model selection.
strength = 0.5  # Example: Use a mid-range model

# 6. temperature: Float controlling LLM randomness.
temperature = 0.0  # Example: Aim for deterministic fixes

# 7. max_attempts: Maximum number of fix attempts.
max_attempts = 5

# 8. budget: Maximum cost allowed for the fixing process (in dollars).
budget = 10.0  # Example budget

# 9. verification_log_file: Path for the verification log file.
verification_log_file = "output/verification_log.txt"

# 10. verbose: Enable detailed logging.
verbose = True

# --- Execute the Function ---
results = fix_verification_errors_loop(
    program_file=str(program_file),
    code_file=str(code_file),
    prompt=prompt,
    verification_program=str(verification_program),
    strength=strength,
    temperature=temperature,
    max_attempts=max_attempts,
    budget=budget,
    verification_log_file=verification_log_file,
    verbose=verbose
)

# --- Display Results ---
print("Results:")
print(f"Success: {results['success']}")
print(f"Final Program:\n{results['final_program']}")
print(f"Final Code:\n{results['final_code']}")
print(f"Total Attempts: {results['total_attempts']}")
print(f"Total Cost: ${results['total_cost']:.2f}")
print(f"Model Name: {results['model_name']}")