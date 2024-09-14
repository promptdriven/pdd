import os
from pdd.cli import cli

def main() -> None:
    """
    Main function to demonstrate the usage of the 'generate' command from the PDD CLI module.
    This example generates runnable code from a prompt file.

    Assumptions:
    - The environment variables are already set.
    - The necessary packages are installed.
    - The 'pdd' module is located in the 'pdd' directory.

    Usage:
    - This script will generate code from a specified prompt file and save it to the specified output location.

    Input:
    - PROMPT_FILE: The path to the prompt file used to generate the code.
    - OUTPUT: The path where the generated code will be saved.

    Output:
    - The generated code is saved to the specified output file.
    - The total cost and model name used for generation are printed to the console.
    """

    # Define the input prompt file and output file paths
    prompt_file: str = "prompts/get_extension_python.prompt"
    output_file: str = "get_extension.py"

    # Set the command line arguments for the 'generate' command
    args: list[str] = [
        "--strength", "0.5",  # Strength of the AI model (0.0 to 1.0)
        "--temperature", "0",  # Temperature of the AI model (0.0 to 1.0)
        "generate",
        "--output", output_file,
        prompt_file,
    ]

    # Execute the CLI command
    try:
        cli.main(args=args)
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()
