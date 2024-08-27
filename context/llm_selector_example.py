import os
from pdd.llm_selector import llm_selector

def main() -> None:
    """
    Main function to demonstrate the usage of the llm_selector function.
    Sets environment variables, defines parameters, and calls the function.
    """
    # Set environment variables (for demonstration purposes)
    os.environ['PDD_MODEL_DEFAULT'] = 'gpt-4o-mini'  # Default model


    # Define desired strength and temperature
    strength: float = .3  # Desired strength of the model (0.0 to 1.0)
    temperature: float = 0  # Temperature for the model (0.0 to 1.0)

    try:
        # Call the llm_selector function
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Output the selected model details
        print(f"Selected LLM: {model_name}")
        print(f"Input Cost: {input_cost}")
        print(f"Output Cost: {output_cost}")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()