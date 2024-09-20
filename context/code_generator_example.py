# Import the code_generator function from the module
from pdd.code_generator import code_generator

def main() -> None:
    """
    Main function to demonstrate the usage of the code_generator function.
    It generates code based on a given prompt using a language model.
    """
    # Define the input parameters for the code_generator function
    # prompt: str = "Create a Python function that calculates the factorial of a number."
    # load the prompt from a file prompts/generate_test_python.prompt
    with open("prompts/generate_test_python.prompt", "r") as file:
        prompt = file.read()
    language: str = "python"
    strength: float = 1  # Strength of the LLM model (0.0 to 1.0)
    temperature: float = 0.5  # Temperature for the LLM model (0.0 to 1.0)

    try:
        # Call the code_generator function
        runnable_code, total_cost, model_name = code_generator(prompt, language, strength, temperature)

        # Output the results
        print("Generated Code:")
        print(runnable_code)
        print(f"Total Cost: ${total_cost:.6f}")
        print(f"Model Name: {model_name}")

    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()
