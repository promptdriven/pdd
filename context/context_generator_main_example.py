import os
import asyncio
from pathlib import Path
import click
from pdd.context_generator_main import context_generator_main

def run_example():
    """
    Demonstrates the usage of context_generator_main to generate example code.
    
    Inputs to context_generator_main:
        - ctx (click.Context): Click context containing global options (strength, temperature, etc.)
        - prompt_file (str): Path to the .prompt file used to generate the original code.
        - code_file (str): Path to the existing source code file.
        - output (Optional[str]): Path to save the generated example. If None, uses default naming.
        - format (Optional[str]): Output format (default: None, uses 'py'). Valid values: 'py' (uses language extension), 'md' (markdown).

    Outputs of context_generator_main:
        - generated_code (str): The resulting example code string.
        - total_cost (float): The cost of the LLM operation in USD.
        - model_name (str): The name of the AI model that performed the generation.
    """
    # 1. Setup directory structure in ./output
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)

    prompt_path = output_dir / "math_utils_python.prompt"
    code_path = output_dir / "math_utils.py"
    example_output_path = output_dir / "math_utils_example.py"

    # 2. Create dummy input files
    prompt_path.write_text(
        "Task: Create a utility for basic math operations.\n"
        "Include a function 'add(a, b)' that returns the sum.",
        encoding="utf-8"
    )
    
    code_path.write_text(
        "def add(a, b):\n    return a + b",
        encoding="utf-8"
    )

    # 3. Mock the Click Context object
    # In a real CLI, this is provided by the @click.group or @click.command decorators
    class MockContext:
        def __init__(self):
            self.obj = {
                'strength': 0.7,        # LLM power (0.0 to 1.0)
                'temperature': 0.2,     # Randomness (0.0 to 1.0)
                'force': True,          # Overwrite existing files
                'quiet': False,         # Show Rich console output
                'verbose': True,        # Detailed logging
                'time': 0.5             # Thinking time budget (0.0 to 1.0)
            }
            self.params = {'local': True} # Force local for this demo to avoid network calls

    ctx = click.Context(click.Command('example'), obj=MockContext().obj)
    ctx.params = {'local': True}

    # 4. Execute the main wrapper
    # This function handles path resolution, preprocessing, cloud/local logic, and syntax fixing
    generated_code, cost, model = context_generator_main(
        ctx=ctx,
        prompt_file=str(prompt_path),
        code_file=str(code_path),
        output=str(example_output_path)
    )

    # 5. Display results
    print(f"--- Generation Results ---")
    print(f"Model Used: {model}")
    print(f"Total Cost: ${cost:.6f}")
    print(f"Output saved to: {example_output_path}")
    print("\nGenerated Code Snippet:")
    print("-" * 20)
    print(generated_code[:150] + "...")

if __name__ == "__main__":
    # Ensure environment variables required by internal modules are present
    # (Normally these are set in the user's shell environment)
    if "NEXT_PUBLIC_FIREBASE_API_KEY" not in os.environ:
        os.environ["NEXT_PUBLIC_FIREBASE_API_KEY"] = "mock_key"
    
    run_example()