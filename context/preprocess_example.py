from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Ensure the project root is in sys.path to allow imports from pdd
# The script is assumed to be in a subdirectory of the project root
project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from pdd.preprocess import preprocess

console = Console()

def main() -> None:
    """
    Demonstrates the usage of pdd.preprocess to prepare LLM prompts.

    The preprocess function handles:
    - <include>tags</include> for file insertion.
    - <include select=\"...\"> for specific code extraction.
    - <shell>cmd</shell> for dynamic command output.
    - Double-curly brace escaping for Template compatibility.
    """

    # 1. Setup: Create sample files to include
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)

    math_file = output_dir / "math_utils.py"
    with open(math_file, "w", encoding="utf-8") as f:
        f.write("""def add(a: int, b: int) -> int:
    \"\"\"Adds two numbers.\"\"\"
    return a + b

def multiply(a: int, b: int) -> int:
    return a * b
""")

    readme_file = output_dir / "README.txt"
    with open(readme_file, "w", encoding="utf-8") as f:
        f.write("This is a sample project documentation.")

    # 2. Define a prompt with various tags
    # - <include>: Inserts entire file
    # - <include select>: Uses ContentSelector to extract only the 'add' function
    # - <shell>: Runs a local command
    # - {variable}: Will be doubled to {{variable}} unless excluded
    raw_prompt = f"""System: You are a coding assistant.

Context from README:
<include>{readme_file}</include>

Here is the math utility (only the add function):
<include select=\"def:add\">{math_file}</include>

Current Directory Listing:
<shell>ls {output_dir}</shell>

User Question: How do I use the {{function_name}} in my code?
Note: Use the template key {{expected_key}}.
"""

    console.print("[bold blue]Original Prompt:[/bold blue]")
    console.print(raw_prompt)
    console.print("-" * 40)

    # 3. Execute Preprocessing
    # Parameters:
    # - prompt (str): The raw text to process.
    # - recursive (bool): If True, resolves tags inside included files.
    # - double_curly_brackets (bool): If True, escapes '{' to '{{' for PromptTemplate safety.
    # - exclude_keys (List[str]): Keys that should NOT be doubled (e.g. for existing variables).
    processed_prompt = preprocess(
        prompt=raw_prompt,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=["expected_key"]
    )

    console.print("[bold green]Preprocessed Prompt Output:[/bold green]")
    console.print(processed_prompt)

    # 4. Demonstrate Recursive Processing
    # Create a file that includes another file
    nested_file = output_dir / "nested.txt"
    with open(nested_file, "w", encoding="utf-8") as f:
        f.write(f"Nested content starts here: <include>{readme_file}</include>")

    recursive_input = f"Main prompt including nested: <include>{nested_file}</include>"

    console.print("\n[bold yellow]Recursive Preprocessing:[/bold yellow]")
    recursive_output = preprocess(recursive_input, recursive=True)
    console.print(recursive_output)

if __name__ == "__main__":
    main()
