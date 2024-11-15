from pdd.postprocess import postprocess
from rich.console import Console

console = Console()

def main() -> None:
    """
    Main function to demonstrate the use of the postprocess function.
    Extracts code from a mixed text and code LLM output and prints the result.
    """
    # Example LLM output containing mixed text and code
    llm_output = """
    Here's a Python function to calculate the factorial:

    ```python
    def factorial(n):
        if n == 0 or n == 1:
            return 1
        else:
            return n * factorial(n-1)
    ```

    You can use this function like this:

    ```python
    result = factorial(5)
    print(f"The factorial of 5 is: {result}")
    ```
    """

    # Specify the programming language and model parameters
    language = "python"
    strength = 0.7  # Strength of the LLM model (0 to 1)
    temperature = 0.2  # Temperature for the LLM model (0 to 1)
    verbose = True

    # Call the postprocess function
    extracted_code, total_cost, model_name = postprocess(llm_output, language, strength, temperature, verbose)

    # Print the extracted code and total cost
    console.print("[bold green]Extracted Code:[/bold green]")
    console.print(extracted_code)
    console.print(f"[bold blue]Total Cost: ${total_cost:.6f}[/bold blue]")
    console.print(f"[bold blue]Model Name: {model_name}[/bold blue]")
    
if __name__ == "__main__":
    main()
