from test_generator import test_generator

# Define the input parameters
prompt: str = "Generate a function, 'add', that takes two arguments, 'a' and 'b', and returns their sum."
code: str = """
def add(a, b):
    return a + b
"""
strength: float = 0.5  # Model selection strength
temperature: float = 0  # Sampling temperature
language: str = "python"  # Programming language of the code

# Call the test_generator function
try:
    unit_test, total_cost = test_generator(prompt, code, strength, temperature, language)

    # Print the results
    print("Generated Unit Test:")
    print(unit_test)
    print(f"Total Cost: ${total_cost:.6f}")
except Exception as e:
    print(f"An error occurred: {e}")