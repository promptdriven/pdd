import os
import click
from pathlib import Path
from rich import print as rprint

# Absolute import assuming the module is located in 'my_module_directory'
from pdd.change_main import change_main

def main() -> None:
    """
    Example usage of the change_main function from the 'pdd' command-line program.

    This example demonstrates how to use the 'change' command in both single-change mode
    and CSV batch-change mode.

    Prerequisites:
    - The 'change_main' module is available and can be imported.
    - All required packages are installed.
    - The environment variables are already set.

    The example will:
    - Create sample input files.
    - Call 'change_main' in single-change mode.
    - Call 'change_main' in CSV batch-change mode based on log example.
    - Display the outputs.
    """

    # Set up the Click context with necessary parameters and options
    ctx = click.Context(click.Command("change"))

    # Set up global options accessible via 'ctx.obj'
    # Adjusted strength and temperature based on log example
    ctx.obj = {
        "force" : True,       # Overwrite existing files (or handle based on needs)
        "quiet" : False,      # Verbose output
        "verbose" : True,     # Detailed output
        "strength": 0.85,     # LLM strength parameter (from log)
        "temperature": 1.0,   # LLM temperature parameter (from log)
        "language": "python", # Programming language for code files
        "extension": ".py",   # File extension for code files
        "budget": 10.0,       # Maximum budget in dollars
    }

    # Create directories for the example
    # os.makedirs("output/example_code_directory", exist_ok=True) # Original single mode dir
    os.makedirs("output/example_output_directory", exist_ok=True)
    os.makedirs("output/single_change_files", exist_ok=True) # Dir for single change example files

    # ------------- Single-Change Mode Example -------------

    # Create sample input files for single-change mode in a specific directory
    single_change_dir = Path("output/single_change_files")
    change_prompt_file = single_change_dir / "change_prompt.prompt"
    input_code_file = single_change_dir / "example_code.py"
    input_prompt_file = single_change_dir / "input_prompt.prompt"
    output_file = single_change_dir / "modified_prompt.prompt" # Output file for single change

    with open(change_prompt_file, "w") as f:
        f.write("Modify the function to add error handling for division by zero.")

    with open(input_code_file, "w") as f:
        f.write("""
def divide(a, b):
    return a / b
""")

    with open(input_prompt_file, "w") as f:
        f.write("Write a function to perform division of two numbers.")

    # Call change_main in single-change mode
    rprint("[bold underline]Single-Change Mode Example[/bold underline]")
    try:
        modified_prompt, total_cost, model_name = change_main(
            ctx=ctx,
            change_prompt_file=str(change_prompt_file),
            input_code=str(input_code_file),
            input_prompt_file=str(input_prompt_file),
            output=str(output_file),
            use_csv=False,  # CSV mode disabled
        )

        # Display the outputs
        rprint(f"\n[bold]Modified Prompt Saved to:[/bold] {output_file}")
        # Optionally read and print modified prompt content if needed
        # with open(output_file, "r") as f:
        #     rprint(f.read())
        rprint(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
        rprint(f"[bold]Model Used:[/bold] {model_name}")
    except Exception as e:
        rprint(f"[bold red]Error in single-change mode:[/bold red] {e}")


    # ------------- CSV Batch-Change Mode Example (Based on Log) -------------

    # Create sample code/prompt files in a directory similar to the log ('change_csv_code')
    code_directory = Path("output/change_csv_code")
    os.makedirs(code_directory, exist_ok=True)

    prompt_file_1 = code_directory / "dummy_a_python.prompt"
    prompt_file_2 = code_directory / "dummy_b_python.prompt"

    with open(prompt_file_1, "w") as f:
        f.write("Write a Python function `func_a(a, b)` that takes two numbers as input and returns their sum.")

    with open(prompt_file_2, "w") as f:
        f.write("Write a Python function `add(a, b)` that takes two numbers as input and returns their sum.")

    code_file_1 = code_directory / "dummy_a.py"
    code_file_2 = code_directory / "dummy_b.py"

    with open(code_file_1, "w") as f:
        f.write("""
def func_a(a, b):
    # Original function A
    return a + b
""")

    with open(code_file_2, "w") as f:
        f.write("""
def add(a, b):
    # Original function B
    return a + b
""")

    # Create a CSV file specifying changes for batch processing
    csv_change_prompt_file = Path("output/batch_changes.csv") # Keep CSV in output dir
    with open(csv_change_prompt_file, "w") as csvfile:
        csvfile.write("prompt_name,change_instructions\n")
        # Use relative paths within the code_directory for prompt_name
        csvfile.write(f"{prompt_file_1.name},Modify the function `func_a` to `func_a_modified`.\n")
        csvfile.write(f"{prompt_file_2.name},Include a comment saying 'Modified B' at the beginning of the function.\n")

    # Define output for batch changes - None, indicating save to input dir (code_directory)
    # Based on log: Output path was a directory, causing an error later.
    # Setting output=None should make change_main save individual modified prompts
    # in the input_code directory (code_directory here).
    batch_output_file = "output/"

    # Call change_main in CSV batch-change mode
    rprint("\n[bold underline]CSV Batch-Change Mode Example (Based on Log)[/bold underline]")
    try:
        message, total_cost_csv, model_name_csv = change_main(
            ctx=ctx,
            change_prompt_file=str(csv_change_prompt_file), # Path to the CSV file
            input_code=str(code_directory), # Directory containing code/prompts
            input_prompt_file=None,  # Not used in CSV mode when paths are in CSV
            output=batch_output_file, # None means save modified prompts individually
            use_csv=True  # CSV mode enabled
        )

        # Display the outputs
        rprint(f"\n[bold]{message}[/bold]")
        rprint(f"[bold]Total Cost:[/bold] ${total_cost_csv:.6f}")
        rprint(f"[bold]Model Used:[/bold] {model_name_csv}")
        # Print the directory where results are saved
        rprint(f"[bold]Batch Results Saved to Directory:[/bold] {code_directory.resolve()}")
    except Exception as e:
        rprint(f"[bold red]Error in CSV batch-change mode:[/bold red] {e}")


if __name__ == "__main__":
    main()
