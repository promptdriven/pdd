from context_generator import context_generator

# Define the parameters for the code generation
code_module: str = "def add(a,b): return a+b"  # The code module to generate examples for
prompt: str = "Create a function that adds two numbers."  # The prompt to guide the example generation
language: str = "python"  # The programming language for the example
strength: float = .9  # The strength parameter for model selection
temperature: float = 0  # The temperature parameter for model selection

try:
    # Call the context_generator function
    example_code, total_cost = context_generator(code_module, prompt, language, strength, temperature)

    # Print the generated example code and total cost
    print("Generated Example Code:")
    print(example_code)
    print(f"Total Cost: ${total_cost:.6f}")
except Exception as e:
    print(f"An error occurred: {e}")