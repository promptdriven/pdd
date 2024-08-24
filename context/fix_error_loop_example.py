from fix_error_loop import fix_error_loop

base = 'change'
# Define the parameters for the function
unit_test_file: str = f'staging/tests/test_{base}.py'  # Path to your unit test file
code_file: str = f'staging/pdd/{base}.py'          # Path to your code file
verification_program: str = f'staging/context/{base}_example.py'          # Path to your verification program
strength: float = 1                            # Strength parameter for error fixing
temperature: float = 0                         # Temperature parameter for error fixing
max_attempts: int = 5                           # Maximum number of attempts to fix errors
budget: float = 100.0                            # Maximum budget for fixing errors
error_log_file = "error_log.txt"  # Path to the error log file

# Call the function
success: bool
final_unit_test_content: str
final_code_content: str
attempts: int
total_cost: float

try:
    success, final_unit_test_content, final_code_content, attempts, total_cost = fix_error_loop(
        unit_test_file,
        code_file,
        verification_program,
        strength,
        temperature,
        max_attempts,
        budget,
        error_log_file=error_log_file
    )

    # Output the results
    if success:
        print("All tests passed successfully!")
    else:
        print("Some tests still failed after attempts.")
    print(f"Final Unit Test Content:\n{final_unit_test_content}")
    print(f"Final Code Content:\n{final_code_content}")
    print(f"Number of Attempts: {attempts}")
    print(f"Total Cost: ${total_cost:.2f}")

except Exception as e:
    print(f"An error occurred: {e}")