from pdd.continue_generation import continue_generation

def main() -> None:
    """
    Main function to demonstrate the usage of the continue_generation function.
    It continues the generation of text using a language model and calculates the cost.
    """
    # Define the input parameters for the continue_generation function
    # formatted_input_prompt: str = "Once upon a time in a land far away, there was a"
    # load context/cli_python_preprocessed.prompt into formatted_input_prompt
    with open("context/cli_python_preprocessed.prompt", "r") as file:
        formatted_input_prompt = file.read()
    
    # llm_output: str = ""  # Initial LLM output is empty
    # load context/unfinished_prompt.txt into llm_output
    with open("context/llm_output_fragment.txt", "r") as file:
        llm_output = file.read()
    strength: float = 1  # Strength parameter for the LLM model
    temperature: float = 0  # Temperature parameter for the LLM model

    try:
        # Call the continue_generation function
        final_llm_output, total_cost, model_name = continue_generation(
            formatted_input_prompt=formatted_input_prompt,
            llm_output=llm_output,
            strength=strength,
            temperature=temperature
        )

        # Output the results
        print(f"Final LLM Output: {final_llm_output}")
        print(f"Total Cost: ${total_cost:.6f}")
        print(f"Model Name: {model_name}")
        # write final_llm_output to context/final_llm_output.txt
        with open("context/final_llm_output.py", "w") as file:
            file.write(final_llm_output)

    except FileNotFoundError as e:
        print(f"Error: {e}")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()