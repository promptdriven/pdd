from pdd.unfinished_prompt import unfinished_prompt

def main() -> None:
    """
    Main function to demonstrate the usage of the unfinished_prompt function.
    It assesses the completeness of a given prompt text using a selected LLM model.
    """
    # Define the prompt text to be analyzed
    prompt_text: str = "Once upon a time in a land far away, there was a"

    # Define the strength and temperature for the LLM model
    strength: float = 0.5  # Strength of the LLM model (0.0 to 1.0)
    temperature: float = 0.0  # Temperature for the LLM model (0.0 to 1.0)

    try:
        # Call the unfinished_prompt function
        reasoning, is_finished, total_cost, model_name = unfinished_prompt(
            prompt_text=prompt_text,
            strength=strength,
            temperature=temperature
        )

        # Output the results
        print(f"Reasoning: {reasoning}")
        print(f"Is Finished: {is_finished}")
        print(f"Total Cost: {total_cost}")
        print(f"Model Name: {model_name}")

    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()