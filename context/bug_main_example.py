import click
from rich import print as rprint
from pdd.bug_main import bug_main

# Create a Click context object
ctx = click.Context(click.Command('bug'))


# Set Click context object attributes
ctx.obj = {
    'force': False,  # Do not overwrite existing files
    'quiet': False,  # Print verbose output
    'strength': 0.9,  # Strength of the AI model (0 to 1)
    'temperature': 0,  # Temperature for the AI model (0 for deterministic output)
}

# Define input file paths and content
prompt_file = "output/factorial_python.prompt"
code_file = "output/factorial.py"
program_file = "output/main.py"

# Create example files
with open(prompt_file, "w") as f:
    f.write("""Write a Python function to calculate the factorial of a number.
The function should be named `factorial` and take a single integer argument.
It should return the factorial of the input number.""")

with open(code_file, "w") as f:
    f.write("""def factorial(n):
    if n == 0:
        return 1
    else:
        return n * factorial(n - 1)""")

with open(program_file, "w") as f:
    f.write("""from factorial import factorial
print(factorial(5))""")

# Define observed and desired outputs
current_output = "120"  # Incorrect output (factorial of 5 is 120, but let's assume it's wrong)
desired_output = "120"  # Correct output

# Call the bug_main function
unit_test, total_cost, model_name = bug_main(
    ctx=ctx,
    prompt_file=prompt_file,
    code_file=code_file,
    program_file=program_file,
    current_output=current_output,
    desired_output=desired_output,
    output="output/test_factorial_bug.py",  # Save the unit test to this file
    language="Python"
)

# Print results
rprint(f"[bold]Generated Unit Test:[/bold]")
rprint(unit_test)
rprint(f"[bold]Total Cost:[/bold] ${total_cost:.6f}")
rprint(f"[bold]Model Used:[/bold] {model_name}")