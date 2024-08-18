from rich.console import Console
from rich.markdown import Markdown
from split import split  

console = Console()

# Example usage of the split function
def main() -> None:
    """
    Main function to demonstrate the usage of the split function.
    """
    # Define input parameters
    input_prompt: str = "Explain the concept of recursion in programming."
    input_code: str = """
    def hello_world():
        print("Hello, World!")
    
    def factorial(n):
        hello_world()
        return 1 if n == 0 else n * factorial(n - 1)"""
    example_code: str = "hello_world()"
    strength: float = 0.7  # Strength parameter for the LLM
    temperature: float = 0  # Temperature parameter for the LLM

    try:
        # Call the split function
        sub_prompt, modified_prompt, total_cost = split(
            input_prompt=input_prompt,
            input_code=input_code,
            example_code=example_code,
            strength=strength,
            temperature=temperature
        )

        # Output the results
        if sub_prompt and modified_prompt:
            console.print(Markdown(f"**Sub Prompt:**\n{sub_prompt}"))
            console.print(Markdown(f"**Modified Prompt:**\n{modified_prompt}"))
            console.print(f"Total Cost: ${total_cost:.6f}")
        else:
            console.print("[bold red]Failed to generate prompts.[/bold red]")
    except Exception as e:
        console.print(f"[bold red]An error occurred: {e}[/bold red]")


if __name__ == "__main__":
    main()