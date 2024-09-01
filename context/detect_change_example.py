from pdd.detect_change import detect_change
from rich.console import Console
from pathlib import Path

console = Console()

# List of prompt files to analyze
prompt_files = [
    "/path/to/prompt1.txt",
    "/path/to/prompt2.txt",
    "/path/to/prompt3.txt"
]
# create a list of all prompt files in the prompts and context directory
prompt_files = [str(prompt_file) for prompt_file in Path("prompts").glob("*.prompt")] + [str(prompt_file) for prompt_file in Path("context").glob("*.prompt")]
print("prompt files", prompt_files)
# Description of the change to be analyzed
change_description = "Use context/python_preamble.prompt to make prompts more compact. Some prompts might already have this."

# LLM model parameters
strength = 1  # Range: 0.0 to 1.0, higher values use stronger (and typically more expensive) models
temperature = 0  # Range: 0.0 to 1.0, higher values increase randomness in the output

try:
    changes_list, total_cost, model_name = detect_change(prompt_files, change_description, strength, temperature)

    console.print("[bold green]Changes detected:[/bold green]")
    for change in changes_list:
        console.print(f"[cyan]Prompt:[/cyan] {change['prompt_name']}")
        console.print(f"[yellow]Instructions:[/yellow] {change['change_instructions']}\n")

    console.print(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
    console.print(f"[bold]Model used:[/bold] {model_name}")

except Exception as e:
    console.print(f"[bold red]An error occurred:[/bold red] {str(e)}")