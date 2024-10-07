import os
from pdd.git_update import git_update

def main() -> None:
    """
    Demonstrate the usage of the git_update_prompt function.
    """
    # Define input parameters
    # input_prompt: str = "Create a function to calculate the area of a circle."
    # load input prompt from file
    name = 'xml_tagger'
    with open(f"prompts/{name}_python.prompt", "r") as file:
        input_prompt = file.read()
    modified_code_file: str = f"pdd/{name}.py"
    strength: float = 0.8  # Strength parameter for the LLM (0.0 to 1.0)
    temperature: float = 0  # Temperature parameter for the LLM

    try:
        # Call the git_update_prompt function
        result = git_update(
            input_prompt=input_prompt,
            modified_code_file=modified_code_file,
            strength=strength,
            temperature=temperature
        )

        if result:
            modified_prompt, total_cost, model_name = result
            print(f"Modified Prompt: {modified_prompt}")
            print(f"Total Cost: ${total_cost:.6f}")  # Cost in dollars
            print(f"Model Name: {model_name}")
        else:
            print("Failed to update the prompt and code.")
            
        # Save the modified prompt to a file
        with open(f"prompts/{name}_python.prompt", "w") as file:
            file.write(modified_prompt)
    except ValueError as e:
        print(f"Input error: {e}")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")

if __name__ == "__main__":
    main()