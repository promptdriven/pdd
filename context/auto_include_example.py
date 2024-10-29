from pdd.auto_include import auto_include
from rich import print as rprint

def main() -> None:
    """
    Main function to demonstrate the use of the auto_include function.
    It processes an input prompt, selects appropriate includes, and displays the results.
    """
    # Example input prompt that needs includes
    input_prompt = """Write a function that calculates the fibonacci sequence."""
    
    # Example list of available include files
    available_includes = [
        "math_utils/fibonacci.md",
        "array_utils/sorting.md",
        "string_utils/parsing.md"
    ]
    
    try:
        # Call auto_include with default strength and temperature
        output_prompt, total_cost, model_name = auto_include(
            input_prompt=input_prompt,
            available_includes=available_includes,
            strength=0.5,  # Controls model capability (0-1)
            temperature=0.7  # Controls randomness in output
        )
        
        # Display results
        rprint("[bold green]Auto-include Results:[/bold green]")
        rprint(f"Model used: {model_name}")
        rprint(f"Total cost: ${total_cost:.6f}")
        rprint("\n[bold]Final Prompt:[/bold]")
        rprint(output_prompt)
        
    except ValueError as e:
        rprint(f"[bold red]Configuration Error:[/bold red] {str(e)}")
    except FileNotFoundError as e:
        rprint(f"[bold red]File Error:[/bold red] {str(e)}")
    except Exception as e:
        rprint(f"[bold red]Unexpected Error:[/bold red] {str(e)}")

if __name__ == "__main__":
    main()