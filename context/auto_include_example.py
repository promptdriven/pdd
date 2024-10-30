from pdd.auto_include import auto_include
from rich.console import Console

# Initialize console for rich printing
console = Console()

def main() -> None:
    """
    Main function to demonstrate the use of the auto_include function.
    It processes an input prompt, selects relevant includes, calculates costs,
    and returns the enhanced prompt with includes, total cost, and model name.
    """
    # Example input prompt that needs includes
    input_prompt = """
    Write a function that calculates the fibonacci sequence.
    Use efficient algorithms and proper error handling.
    """
    
    # Example list of available include files
    available_includes = [
        "algorithms/math_utils.py",
        "utils/error_handling.py",
        "algorithms/fibonacci.py",
        "data_structures/arrays.py"
    ]
    
    # Set model parameters
    strength = 0.7  # 0-1 scale, higher means stronger model
    temperature = 0.2  # 0-1 scale, lower means more deterministic
    
    try:
        # Call auto_include function
        output_prompt, total_cost, model_name = auto_include(
            input_prompt=input_prompt,
            available_includes=available_includes,
            strength=strength,
            temperature=temperature
        )
        
        # Display results
        console.print("\n[bold green]Results:[/]")
        console.print(f"Selected Model: {model_name}")
        console.print(f"Total Cost: ${total_cost:.6f}")
        console.print("\n[bold]Final Prompt with Includes:[/]")
        console.print(output_prompt)
        
    except ValueError as e:
        console.print(f"[bold red]Value Error: {str(e)}[/]")
    except FileNotFoundError as e:
        console.print(f"[bold red]File Error: {str(e)}[/]")
    except Exception as e:
        console.print(f"[bold red]Unexpected Error: {str(e)}[/]")

if __name__ == "__main__":
    main()