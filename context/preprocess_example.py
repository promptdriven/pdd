from __future__ import annotations

import os
import shutil
from pathlib import Path
from rich.console import Console
from pdd.preprocess import preprocess

console = Console()

def main() -> None:
    """Run the preprocessing example demonstrating file inclusion and brace doubling."""
    # Create the output directory relative to the current working directory
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # Create a dummy helper file to include in our prompt
    helper_file = output_dir / "helper.py"
    helper_content = """def greet(name: str) -> str:\n    return f\"Hello, {name}!\"\n"""
    helper_file.write_text(helper_content, encoding="utf-8")

    # Define a prompt with XML-like include tags and single curly braces
    # that we want to double (to avoid template conflicts later)
    prompt_template = f"""Below is our helper utility code:

<include>{str(helper_file)}</include>

Ensure you implement the client using the following JSON schema:
{{
    \"username\": \"string\",
    \"active\": \"boolean\"
}}
"""

    console.print("[bold blue]Original Prompt Template:[/bold blue]")
    console.print(prompt_template)

    # Run the preprocessor
    # - double_curly_brackets=True doubles single '{' and '}' (except inside specified exclusions)
    # - compress=False keeps the full included file content
    processed_prompt = preprocess(
        prompt=prompt_template,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=None,
        compress=False,
    )

    console.print("[bold green]Preprocessed Prompt Output:[/bold green]")
    console.print(processed_prompt)

    # Clean up - use rmtree to handle any auxiliary files (e.g. __pycache__)
    if output_dir.exists():
        shutil.rmtree(output_dir, ignore_errors=True)

if __name__ == "__main__":
    main()