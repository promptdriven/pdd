from context_generator import context_generator


# Define the parameters for the context generator
code_module: str = f"""def factorial(n):
    # Base case: factorial of 0 or 1 is 1
    if n == 0 or n == 1:
        return 1
    # Recursive case: n * factorial of (n-1)
    else:
        return n * factorial(n - 1)"""
prompt: str = "Generate a function to calculate the factorial of a number."
language: str = "python"
strength: float = 0.7
temperature: float = 0.5

# Call the context_generator function
try:
    example_code, total_cost = context_generator(
        code_module=code_module,
        prompt=prompt,
        language=language,
        strength=strength,
        temperature=temperature
    )

    # Print the generated example code and total cost
    print("Generated Example Code:")
    print(example_code)
    print(f"Total Cost: ${total_cost:.6f}")

except Exception as e:
    print(f"An error occurred: {e}")