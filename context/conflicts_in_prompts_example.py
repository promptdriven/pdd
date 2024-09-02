from pdd.conflicts_in_prompts import conflicts_in_prompts
from rich import print as rprint

def main() -> None:
    """
    Main function to demonstrate the usage of the conflicts_in_prompts function.
    It defines two example prompts, calls the function, and prints the results.
    """
    # Example prompts
    prompt1: str = "Write a story about a happy dog."
    prompt2: str = "Write a story about a sad cat."

    # Call the function
    conflicts, total_cost, model_name = conflicts_in_prompts(prompt1, prompt2, strength=0.7, temperature=0.2)

    # Print the results
    rprint("[bold]Conflicts found:[/bold]")
    for conflict in conflicts:
        rprint(f"Description: {conflict['description']}")
        rprint(f"Explanation: {conflict['explanation']}")
        rprint(f"Suggestion for prompt1: {conflict['suggestion1']}")
        rprint(f"Suggestion for prompt2: {conflict['suggestion2']}")
        rprint("---")

    rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
    rprint(f"[bold]Model used:[/bold] {model_name}")

if __name__ == "__main__":
    main()