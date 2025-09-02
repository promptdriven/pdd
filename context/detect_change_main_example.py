import click
from pdd.detect_change_main import detect_change_main
import os

def main():
    """
    Main function to simulate CLI parameters and call the detect_change_main function.
    """
    # Create a Click context object to simulate CLI parameters
    ctx = click.Context(click.Command('detect_change_main'))
    # ctx.params = {'force': False, 'quiet': False}  # Default CLI options
    ctx.obj = {'strength': 0.5, 'temperature': 0, 'force': False, 'quiet': False}  # Model parameters

    # Define the list of prompt files and the change description file
    prompt_files = [
        "context/python_preamble.prompt",
        "prompts/change_python.prompt",
        "prompts/fix_error_loop_python.prompt",
        "prompts/code_generator_python.prompt"
    ]
    change_file = "output/change_description.prompt"

    # write the change description to the change file
    with open(change_file, 'w') as file:
        file.write("Use context/python_preamble.prompt to make prompts more compact. Some prompts might already have this.")

    # Optional output file path
    output = "output/detect_results.csv"

    # Ensure the output directory exists
    os.makedirs(os.path.dirname(output), exist_ok=True)

    try:
        # Call the detect_change_main function
        changes_list, total_cost, model_name = detect_change_main(
            ctx=ctx,
            prompt_files=prompt_files,
            change_file=change_file,
            output=output
        )

        # Print the results
        print(f"Model used: {model_name}")
        print(f"Total cost: ${total_cost:.6f}")
        print("Changes needed:")
        for change in changes_list:
            print(f"Prompt: {change['prompt_name']}")
            print(f"Instructions: {change['change_instructions']}")
            print("---")

    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()