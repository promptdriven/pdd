import click
from pathlib import Path

# Import the auto_deps_main function from your module
from pdd import auto_deps_main


def main():
    """
    Main function to demonstrate the usage of `auto_deps_main`.

    This function sets up the necessary parameters and calls `auto_deps_main` to process
    an input prompt file, analyze dependencies, and generate an output with the dependencies
    inserted.

    Args:
        None

    Returns:
        None
    """
    # Initialize the Click context with command-line options
    ctx = click.Context(click.Command('auto-deps'))
    ctx.params = {
        'force': False,   # Set to True to force file overwrites
        'quiet': False    # Set to True to suppress output messages
    }
    # Context object containing additional parameters
    ctx.obj = {
        'strength': 0.9,      # Strength parameter for dependency analysis
        'temperature': 0.0    # Temperature parameter for dependency analysis
    }

    # Define the input parameters
    prompt_file = 'path/to/your/prompt_file.txt'
    """
    The path to the input prompt file that you want to process.
    This file should contain the prompt where dependencies need to be analyzed and inserted.
    """

    directory_path = 'path/to/dependency/files'
    """
    The path to the directory containing potential dependency files.
    This can include glob patterns, e.g., "context/*_example.py", to specify multiple files.
    """

    auto_deps_csv_path = 'path/to/auto_deps.csv'
    """
    (Optional) The path to the CSV file containing auto-dependency information.
    If not provided, a default path "project_dependencies.csv" will be used.
    """

    output = 'path/to/modified_prompt.txt'
    """
    (Optional) The path to save the modified prompt file with auto-dependencies inserted.
    If not provided, the original prompt file will be overwritten if 'force' is True.
    """

    force_scan = False
    """
    (Optional) Flag to force a rescan of the directory for dependencies.
    Set to True to ignore cached results and rescan.
    """

    # Call the auto_deps_main function with the parameters
    try:
      modified_prompt, total_cost, model_name = auto_deps_main(
          ctx=ctx,
          prompt_file=prompt_file,
          directory_path=directory_path,
          auto_deps_csv_path=auto_deps_csv_path,
          output=output,
          force_scan=force_scan
      )

      # Display the results
      print("Modified Prompt:")
      print(modified_prompt)
      print(f"Total Cost: ${total_cost:.6f}")
      print(f"Model Used: {model_name}")
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    main()