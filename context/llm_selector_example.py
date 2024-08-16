import os
from llm_selector import llm_selector


def main() -> None:
    """
    Main function to demonstrate the usage of the llm_selector function.
    Sets up environment variables, calls the llm_selector function, and prints the results.
    """
    try:
        # Set environment variables for the example
        # os.environ['PDD_PATH'] = '/path/to/your/data'  # Update this path to your actual data directory
        os.environ['PDD_MODEL_DEFAULT'] = 'gpt-4o-mini'  # Set your default model

        # Input parameters
        strength: float = 0.7  # Strength of the model selection (0.0 to 1.0)
        temperature: float = 0.5  # Temperature for the model (controls randomness)

        # Get the selected LLM and related information
        llm, token_counter, input_cost, output_cost = llm_selector(strength, temperature)
        sample_text = "Sample text for token counting."
        token_count = token_counter(sample_text)

        # Output the results
        print(f"Selected LLM: {llm}")
        print(f"Token Counter: {token_counter}")
        print(f"Counting tokens in the following text: '{sample_text}'")
        print(f"The number of tokens in the text is: {token_count}")
        print(f"Input Cost: {input_cost} per million tokens")
        print(f"Output Cost: {output_cost} per million tokens")
    except Exception as e:
        print(f"An error occurred: {e}")


if __name__ == "__main__":
    main()