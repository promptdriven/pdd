from pdd.incremental_code_generator import incremental_code_generator
from pdd import DEFAULT_STRENGTH
from rich.console import Console
from rich.markdown import Markdown

console = Console()

def main():
    """
    Example usage of the incremental_code_generator from the `pdd` package.
    
    This script demonstrates how to perform an incremental code update given:
    - An original prompt,
    - An updated prompt,
    - Previously generated code,
    - And a target programming language (e.g., 'python').
    
    The script decides whether to regenerate the code from scratch or apply a structured, minimal diff
    to the existing code using internal language model (LLM) tools.

    Returns:
        None. All results printed to the Rich console.
    """

    # --- INPUT PARAMETERS ---
    
    # Description of task changes
    original_prompt = "Write a Python function to calculate the factorial of a number."
    new_prompt = "Write a Python function to calculate the factorial with input validation (must be non-negative)."
    
    # Original code that was generated (based on original_prompt)
    existing_code = """
def factorial(n):
    if n == 0 or n == 1:
        return 1
    return n * factorial(n - 1)
"""

    # Language of the source code
    language = "python"

    # Strength [0.0 – 1.0] — how "precise" or "bold" the LLM should be
    strength = DEFAULT_STRENGTH

    # Temperature [0.0 – 1.0] — determines randomness in generation
    temperature = 0.0

    # Time budget [0.0 – 1.0] — higher values may allow more reasoning (unitless)
    time = 0.25

    # If True, force patching even when large structural changes are detected
    force_incremental = False

    # Show detailed output from each step
    verbose = True

    # Should the input prompt templates be preprocessed (for prompt standardization)?
    preprocess_prompt = True

    # --- RUN ---
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

    # --- OUTPUT ---
    console.rule("[bold magenta]Update Result[/bold magenta]")

    if is_incremental:
        console.print("[bold green]Incremental patching was applied successfully.[/bold green]")
        console.print(Markdown("### Updated Code:\n```python\n{}\n```".format(updated_code.strip())))
    else:
        console.print("[bold yellow]Full regeneration is recommended due to major changes.[/bold yellow]")
        console.print("No incremental patch was generated; caller should regenerate the code from scratch.")

    console.print()
    console.print(f"[bold blue]Total Cost Incurred:[/bold blue] ${total_cost:.6f} (in dollars)")
    console.print(f"[bold blue]Model Used:[/bold blue] {model_name}")

if __name__ == "__main__":
    main()