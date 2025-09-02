from pdd.trace_main import trace_main
import click

# Create example files
prompt_content = """
# Prompt for a simple calculator
Create a Python function that:
1. Takes two numbers as input
2. Adds them together
3. Returns the result
"""

code_content = """
def add_numbers(a: float, b: float) -> float:
    # Add two numbers together
    return a + b

result = add_numbers(5.0, 3.0)
print(f"The sum is: {result}")
"""

# Write example files
with open("output/calculator.prompt", "w") as f:
    f.write(prompt_content)
with open("output/calculator.py", "w") as f:
    f.write(code_content)

# Create a Click context with configuration
ctx = click.Context(click.Command("trace"))
ctx.obj = {
    'quiet': False,  # Set to True to suppress console output
    'force': True,   # Set to True to overwrite existing output files
    'strength': 0.7, # Controls LLM analysis strength (0.0 to 1.0)
    'temperature': 0.0 # Controls LLM randomness (0.0 to 1.0)
}

# Call trace_main
try:
    prompt_line, total_cost, model_name = trace_main(
        ctx=ctx,
        prompt_file="output/calculator.prompt",
        code_file="output/calculator.py",
        code_line=2,  # Line number to trace (the add_numbers function definition)
        output="output/trace_results.txt"  # Optional: save results to file
    )

    print(f"Prompt line number: {prompt_line}")  # Line in prompt file corresponding to code
    print(f"Analysis cost: ${total_cost:.6f}")   # Cost in USD
    print(f"Model used: {model_name}")           # Name of the LLM model used
except Exception as e:
    print(f"An error occurred: {e}")