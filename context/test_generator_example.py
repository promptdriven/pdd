from test_generator import test_generator

# Define the input parameters
prompt: str = "Create an additon function that takes two arguments and returns their sum."
code: str = """
def add(a, b):
    return a + b
"""
strength: float = 1  # Model strength parameter
temperature: float = 0.5  # Temperature parameter for randomness
language: str = "python"  # Programming language of the code

# Call the test_generator function
unit_test_code, total_cost = test_generator(prompt, code, strength, temperature, language)

# Print the results
print("Generated Unit Test Code:")
print(unit_test_code)
print(f"Total Cost of Operation: ${total_cost:.6f}")