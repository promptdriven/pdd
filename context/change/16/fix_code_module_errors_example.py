from pdd.fix_code_module_errors import fix_code_module_errors

def main():
    # Original program with an error
    program_with_error = """
def calculate_sum(numbers):
    return sum(numbers)

result = calculate_sum("123")  # Error: trying to sum a string
print(result)
"""

    # Original prompt that generated the code
    original_prompt = "Write a function that calculates the sum of numbers"

    # Original code module with the error
    code_module = """
def calculate_sum(numbers):
    return sum(numbers)
"""

    # Error message received when running the program
    error_message = """
TypeError: unsupported operand type(s) for +: 'int' and 'str'
  File "example.py", line 4, in <module>
    result = calculate_sum("123")
  File "example.py", line 2, in calculate_sum
    return sum(numbers)
"""

    # Call the function to fix the errors
    update_program, update_code, fixed_program, fixed_code, total_cost, model_name = fix_code_module_errors(
        program=program_with_error,    # The program containing the error (str)
        prompt=original_prompt,        # The original prompt used to generate the code (str)
        code=code_module,             # The code module containing the error (str)
        errors=error_message,         # The error message received (str)
        strength=0.7,                 # Model strength (float between 0-1, higher = stronger model)
        temperature=0                 # Temperature for model output (float, 0 = deterministic)
    )

    """
    Returns:
        update_program (bool): Whether the program needs updating
        update_code (bool): Whether the code module needs updating
        fixed_program (str): The fixed program code
        fixed_code (str): The fixed code module
        total_cost (float): Total cost in USD for the API calls
        model_name (str): Name of the model used for fixing
    """

    # Print the results
    print(f"Program needs update: {update_program}")
    print(f"Code needs update: {update_code}")
    print(f"\nFixed program:\n{fixed_program}")
    print(f"\nFixed code module:\n{fixed_code}")
    print(f"\nTotal cost: ${total_cost:.4f}")
    print(f"Model used: {model_name}")

if __name__ == "__main__":
    main()