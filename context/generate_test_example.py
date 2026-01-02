import os
from rich import print
from pdd.generate_test import generate_test

# Ensure the output directory exists
output_dir = "./output"
os.makedirs(output_dir, exist_ok=True)

def main():
    """
    Demonstrates how to use the generate_test function to create a unit test
    for a given piece of code using an LLM.
    """
    
    # 1. Define the code you want to test
    # In a real scenario, this might be read from a file.
    code_to_test = """
def calculate_fibonacci(n: int) -> int:
    if n < 0:
        raise ValueError("Input must be non-negative")
    if n <= 1:
        return n
    return calculate_fibonacci(n - 1) + calculate_fibonacci(n - 2)
"""

    # 2. Define the prompt that supposedly generated this code
    # This helps the LLM understand the intent behind the code.
    original_prompt = "Write a recursive function to calculate the nth Fibonacci number."

    # 3. Set up parameters
    # strength: 0.0 to 1.0 (higher = more powerful model)
    # temperature: 0.0 to 1.0 (higher = more creative/random)
    strength = 0.5
    temperature = 0.2
    
    print(f"[bold blue]Generating test for code:[/bold blue]\n{code_to_test.strip()}")

    # 4. Call the generate_test function
    # This function handles prompt loading, LLM invocation, continuation (if cut off),
    # and post-processing to extract just the code.
    unit_test_code, cost, model_used = generate_test(
        prompt=original_prompt,
        code=code_to_test,
        strength=strength,
        temperature=temperature,
        language="python",
        verbose=True,  # Set to True to see the generation process in the console
        module_name="fibonacci_utils", # Helps with import statements in the generated test
        test_file_path="tests/test_fib.py" # Helps context for file structure
    )

    # 5. Output the results
    print("\n[bold green]Generation Complete![/bold green]")
    print(f"Model Used: [cyan]{model_used}[/cyan]")
    print(f"Total Cost: [cyan]${cost:.6f}[/cyan]")
    
    # 6. Save the generated test to a file
    output_file = os.path.join(output_dir, "test_fibonacci.py")
    with open(output_file, "w") as f:
        f.write(unit_test_code)
        
    print(f"\n[bold]Generated Test Code (saved to {output_file}):[/bold]")
    print(unit_test_code)

if __name__ == "__main__":
    main()