from pdd.incremental_code_generator import incremental_code_generator
from rich.console import Console
import os

console = Console()

def main():
    """Example usage of incremental_code_generator with detailed input/output handling."""

    # Load required inputs from files
    # Ensure these files exist in the 'output/' directory relative to where this script is run.
    # For example, if this script is in 'project_root/', then the files should be in 'project_root/output/'.
    
    # Create dummy files if they don't exist for the example to run
    os.makedirs("output", exist_ok=True)
    if not os.path.exists("output/test_original_prompt.txt"):
        with open("output/test_original_prompt.txt", "w") as f:
            f.write("Write a Python function that checks if a string is a palindrome.")
    
    if not os.path.exists("output/test_new_prompt.txt"):
        with open("output/test_new_prompt.txt", "w") as f:
            f.write("Write a Python function that checks if a string is a palindrome. Ignore punctuation and casing during the check.")
            
    if not os.path.exists("output/test_existing_code.py"):
        with open("output/test_existing_code.py", "w") as f:
            f.write("def is_palindrome(s: str) -> bool:\n    return s == s[::-1]")

    with open("output/test_original_prompt.txt", "r") as f:
        original_prompt: str = f.read()

    with open("output/test_new_prompt.txt", "r") as f:
        new_prompt: str = f.read()

    with open("output/test_existing_code.py", "r") as f:
        existing_code: str = f.read()

    language: str = "python"           # Programming language of the code
    strength: float = 0.9                # Relative model strength, [0, 1]
    temperature: float = 0.0             # Controls randomness, [0, 1]
    time: float = 0.25                   # Reasoning budget, [0, 1]
    force_incremental: bool = False     # Whether to override full regeneration
    verbose: bool = True                # Show debug output
    preprocess_prompt: bool = True     # Whether to preprocess prompts

    # Call the function
    updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
        original_prompt=original_prompt,
        new_prompt=new_prompt,
        existing_code=existing_code,
        language=language,
        strength=strength,
        temperature=temperature,
        time=time,
        force_incremental=force_incremental,
        verbose=verbose,
        preprocess_prompt=preprocess_prompt
    )

    # Output results
    console.rule("[bold blue]incremental_code_generator Output")
    console.print(f"[bold green]Was Incremental?:[/bold green] {is_incremental}")
    console.print(f"[bold green]Total LLM Cost:[/bold green] ${total_cost:.6f} (e.g., dollars per 1M tokens)")
    console.print(f"[bold green]Used Model:[/bold green] {model_name}")
    console.rule("[bold green]Updated Code")
    console.print(updated_code)

if __name__ == "__main__":
    main()
