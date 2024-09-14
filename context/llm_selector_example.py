from pdd.llm_selector import llm_selector

def main() -> None:
    """
    Main function to demonstrate the usage of the llm_selector function.
    """
    # Define the strength and temperature parameters
    temperature: float = 1  # Example temperature value for the LLM model

    try:
        # for loop to iterate over different strengths from 0 to 1 with a step of 0.1
        for strength in [i * 0.1 for i in range(5,11)]:
            # Call the llm_selector function with the specified strength and temperature
            llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

            # Print the details of the selected LLM model
            print(f"Selected LLM Model: {model_name}")
            print(f"Input Cost per Million Tokens: {input_cost}")
            print(f"Output Cost per Million Tokens: {output_cost}")

            # Example usage of the token counter function
            sample_text: str = "This is a sample text to count tokens."
            token_count: int = token_counter(sample_text)
            print(f"Token Count for Sample Text: {token_count}")
            print(f"model_name: {model_name}")

    except FileNotFoundError as e:
        print(f"Error: {e}")
    except ValueError as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    main()
