import os
import pandas as pd
from pdd.auto_include import auto_include

def main() -> None:
    """
    Example usage of the auto_include function.
    """
    # load output.csv
    csv_file = pd.read_csv("output.csv")

    # Define the parameters for the auto_include function
    input_prompt = "Please include the necessary dependencies for the following code."
    directory_path = "context/c*.py"
    # read in the file
    with open('output.csv', 'r') as file:
        csv_file = file.read()
    strength = 0.7
    temperature = 0.5
    verbose = True

    # Call the auto_include function
    output_prompt, csv_output, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        directory_path=directory_path,
        csv_file=csv_file,
        strength=strength,
        temperature=temperature,
        verbose=verbose
    )

    # Print the results
    print("Output Prompt:")
    print(output_prompt)
    print(f"Total Cost: ${total_cost:.4f} (in dollars per million tokens)")
    print(f"Model Name: {model_name}")

if __name__ == "__main__":
    main()