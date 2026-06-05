from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Ensure the package is importable
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from pdd.preprocess import preprocess

console = Console()


def main() -> None:
    # Create the output directory for our example files
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a dummy configuration/code file to include
    config_file = output_dir / "config_schema.py"
    config_file.write_text("""# Configuration Schema
class AppConfig:
    def __init__(self, port: int = 8080):
        self.port = port
        self.debug = True
""", encoding="utf-8")

    # 2. Create a dummy documentation markdown file
    doc_file = output_dir / "api_docs.md"
    doc_file.write_text("""# API Reference
This endpoint returns the system status.
""", encoding="utf-8")

    console.print("[bold blue]Created dummy files in ./output for inclusion:[/bold blue]")
    console.print(f" - {config_file}")
    console.print(f" - {doc_file}\n")

    # 3. Define a prompt that utilizes different preprocessing features:
    # - <include> tags for explicit files
    # - Backtick includes: ```<path>```
    # - Single braces that need to be doubled for standard LLM templating engines
    # - Excluded keys that should NOT be doubled
    prompt_template = """You are an expert assistant.

Here is our configuration class:
<include select="class:AppConfig" mode="full">./output/config_schema.py</include>

Here is our API reference:
```<./output/api_docs.md>```

Some variables that will be formatted later by a template engine:
- Current user: {user_name}
- API Key: {api_key}  <!-- This should remain single-braced because we exclude it -->
- Some JSON syntax: {"key": "value"}
"""

    console.print("[bold yellow]Original Prompt Template:[/bold yellow]")
    console.print(prompt_template)
    console.print("-" * 40)

    # 4. Run the preprocessor
    # Parameters Explained:
    # - prompt: The input string containing tags and braces.
    # - recursive: If True, recursively pre-processes nested includes (defers shell/web/include-many).
    # - double_curly_brackets: Automatically escapes single '{' and '}' to '{{' and '}}' to avoid breaking template formatters.
    # - exclude_keys: A list of keys inside single braces that should NOT be doubled.
    # - compress: Activates context compression modes on applicable inclusions.
    # - examples_dir / tests_dir: Directories used for applying auto-compression policies.
    preprocessed_prompt = preprocess(
        prompt=prompt_template,
        recursive=False,
        double_curly_brackets=True,
        exclude_keys=["api_key"],  # Preserve {api_key} exactly as-is
        compress=False,
    )

    console.print("[bold green]Preprocessed Prompt Output:[/bold green]")
    console.print(preprocessed_prompt)


if __name__ == "__main__":
    main()