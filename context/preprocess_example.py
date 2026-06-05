"""Example of using the pdd.preprocess module to prepare prompts for LLMs."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console
from pdd.preprocess import preprocess

# Initialize rich console for beautiful output
console = Console()


def create_dummy_files(output_dir: Path) -> None:
    """Create sample files in the output directory to simulate includes."""
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Standard code file to include
    code_content = """def greet(name: str) -> str:
    \"\"\"Return a friendly greeting.\"\"\"
    return f"Hello, {name}!"
"""
    (output_dir / "utils.py").write_text(code_content, encoding="utf-8")

    # 2. Configuration file
    config_content = """{
    "temperature": 0.2,
    "max_tokens": 1024
}"""
    (output_dir / "config.json").write_text(config_content, encoding="utf-8")


def main() -> None:
    # Ensure our working environment has dummy include targets
    output_dir = Path("./output")
    create_dummy_files(output_dir)

    console.print(
        "[bold blue]Starting pdd.preprocess example execution...[/bold blue]"
    )

    # Define a prompt template utilizing various preprocessing features:
    # - <include> tag for files
    # - Backtick includes for quick file embedding: ```<path>```
    # - <shell> tags for dynamic command execution
    # - Single curly braces that will be escaped/doubled (to protect them from
    #   external template formatters like Jinja or LangChain's PromptTemplate)
    prompt_template = """System: You are an expert system.

Here is our configuration:
<include>output/config.json</include>

Here are our helper utilities:
```<output/utils.py>```

We are running on the following OS platform:
<shell>python -c "import platform; print(platform.system())"</shell>

JSON format instruction:
The user output must match this schema: { "status": "success", "data": { "key": "value" } }.
This single brace variable {user_name} should be doubled except if excluded.
"""

    console.print("\n[bold]Original Prompt Template:[/bold]")
    console.print(prompt_template, style="dim")

    # Call preprocess with:
    # - double_curly_brackets=True: single braces like { "status": "success" }
    #   become double braces {{ "status": "success" }} so Python's .format()
    #   doesn't break on them.
    # - exclude_keys=["user_name"]: exact match '{user_name}' will NOT be doubled.
    preprocessed_prompt = preprocess(
        prompt=prompt_template,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=["user_name"],
        compress=False,
    )

    console.print("\n[bold green]Successfully Preprocessed Prompt:[/bold green]")
    console.print(preprocessed_prompt)


if __name__ == "__main__":
    main()