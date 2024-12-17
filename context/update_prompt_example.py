import os
from tabnanny import verbose
from pdd.update_prompt import update_prompt

def main() -> None:
    """
    Main function to demonstrate the usage of the update_prompt function.
    """
    # Define the input parameters
    input_prompt = "Please add two numbers and return the sum."
    input_code = "def add(a, b): return a + b"
    modified_code = "def mul_numbers(x, y): return x * y"
    strength = 0.9  # Example strength parameter for the LLM
    temperature = 0  # Example temperature parameter for the LLM

    try:
        # Call the update_prompt function
        modified_prompt, total_cost, model_name = update_prompt(
            input_prompt=input_prompt,
            input_code=input_code,
            modified_code=modified_code,
            strength=strength,
            temperature=temperature,
            verbose=True
        )

        # Check the results
        if modified_prompt is not None:
            print(f"Modified Prompt: {modified_prompt}")
            print(f"Total Cost: ${total_cost:.6f}")
            print(f"Model Name: {model_name}")
        else:
            print("Failed to update the prompt.")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()