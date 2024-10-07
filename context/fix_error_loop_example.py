from pdd.fix_error_loop import fix_error_loop
from rich import print as rprint
from rich.panel import Panel

def main() -> None:
    """
    Main function to demonstrate the usage of the fix_error_loop function.
    It sets up the parameters, calls the function, and prints the results.
    """
    # Define input parameters
    base = 'conflicts_main'
    # Define the parameters for the function
    unit_test_file: str = f'tests/test_{base}.py'  # Path to your unit test file
    code_file: str = f'pdd/{base}.py'          # Path to your code file
    # load the prompt from the prompt file
    with open(f'prompts/{base}_python.prompt', 'r') as file:
        prompt = file.read()
    verification_program: str = f'context/{base}_example.py'          # Path to your verification program
    strength: float = 1                            # Strength parameter for error fixing
    temperature: float = 1                        # Temperature parameter for error fixing
    max_attempts: int = 5                           # Maximum number of attempts to fix errors
    budget: float = 100.0                            # Maximum budget for fixing errors
    error_log_file = "error.log"  # Path to the error log file

    try:
        # Call the fix_error_loop function
        success, final_unit_test, final_code, total_attempts, total_cost, model_name = fix_error_loop(
            unit_test_file, code_file, prompt, verification_program,
            strength, temperature, max_attempts, budget, error_log_file
        )

        # Print the results
        rprint(Panel.fit(f"Success: {success}"))
        rprint(Panel.fit(f"Total attempts: {total_attempts}"))
        rprint(Panel.fit(f"Total cost: ${total_cost:.6f}"))
        rprint(Panel.fit(f"Model used: {model_name}"))

        rprint(Panel.fit(f"Final Unit Test: {final_unit_test}"))
        rprint(Panel.fit(f"Final Code: {final_code}"))
    except Exception as e:
        rprint(Panel.fit(f"An error occurred: {e}"))

if __name__ == "__main__":
    main()
