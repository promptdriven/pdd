import os
from your_module import change  # Replace 'your_module' with the actual module name

def main() -> None:
    """
    Main function to demonstrate the usage of the `change` function.
    """
    # Define input parameters
    input_prompt: str = "What is the capital of France?"
    input_code: str = "print('Hello, World!')"
    change_prompt: str = "Make the question more specific."
    strength: float = 0.7  # Adjust the strength of the model
    temperature: float = 0.5  # Adjust the randomness of the output

    try:
        # Call the change function
        modified_prompt, total_cost, model_name = change(
            input_prompt, input_code, change_prompt, strength, temperature
        )

        # Print the results
        print(f"Modified Prompt: {modified_prompt}")
        print(f"Total Cost: ${total_cost:.6f}")
        print(f"Model Name: {model_name}")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()