from pathlib import Path
from rich import print
from rich.console import Console
from pdd.insert_includes import insert_includes

def example_usage() -> None:
    """
    Example usage of the insert_includes module to process dependencies.
    Demonstrates input setup, error handling, and result display.
    """
    # Initialize console for rich output
    console = Console()

    # Define input parameters
    input_prompt = """
    Write a Python function that:
    1. Reads a CSV file
    2. Processes the data
    3. Outputs results to a new file
    """

    directory_path = "context/*_example.py"  # Directory containing relevant files
    csv_filename = "project_dependencies.csv"  # CSV file with dependency information

    try:
        # Call insert_includes with custom parameters
        output_prompt, csv_output, total_cost, model_name = insert_includes(
            input_prompt=input_prompt,
            directory_path=directory_path,
            csv_filename=csv_filename,
            strength=0.93,  # Higher strength for more focused output
            temperature=0,  # Lower temperature for more consistent results
            verbose=True
        )

        # Display results
        console.print("\n[bold green]Successfully processed dependencies![/bold green]")
        console.print("\n[yellow]Original Prompt:[/yellow]")
        console.print(input_prompt)

        console.print("\n[yellow]Modified Prompt with Dependencies:[/yellow]")
        console.print(output_prompt)

        console.print(f"\n[yellow]CSV Output:[/yellow]\n{csv_output}")
        console.print(f"[yellow]Model Used:[/yellow] {model_name}")
        console.print(f"[yellow]Total Cost:[/yellow] ${total_cost:.4f}")
        
        # Save the csv file
        csv_path = Path(csv_filename)
        csv_path.write_text(csv_output)

    except FileNotFoundError:
        console.print("[red]Error: Dependencies CSV file not found![/red]")
    except Exception as e:
        console.print(f"[red]Error during processing: {str(e)}[/red]")

if __name__ == "__main__":
    example_usage()