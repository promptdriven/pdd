from code_generator import code_generator


def main() -> None:
    """
    Main function to demonstrate the usage of the code_generator function.
    It defines the input parameters, calls the code_generator, and prints the results.
    """
    # Define the input parameters
    prompt: str = "Create a function that calculates the factorial of a number."
    language: str = "python"
    strength: float = 0.8
    temperature: float = 0.5

    try:
        # Call the code_generator function
        runnable_code, total_cost = code_generator(prompt, language, strength, temperature)

        # Print the results
        print("Generated Code:")
        print(runnable_code)
        print(f"Total Cost: ${total_cost:.6f}")
    except Exception as e:
        print(f"An error occurred: {e}")


if __name__ == "__main__":
    main()
