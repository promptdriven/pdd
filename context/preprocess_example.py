from pdd.preprocess import preprocess
from rich.console import Console
console = Console()

# --- Basic tag processing ---
prompt = """
<prompt>
    <shell>echo Hello World</shell>
    <pdd>This is a comment</pdd>
    <web>https://www.google.com</web>
    {test}
    {test2}
    ```<TODO.md>```

    <pdd>
        multi-line
        comment should not show up
    </pdd>
</prompt>
"""

recursive = False
double_curly_brackets = True
exclude_keys = ["test2"] # exclude test2 from being doubled

# Debug info
console.print(f"[bold yellow]Debug: exclude_keys = {exclude_keys}[/bold yellow]")

processed = preprocess(prompt, recursive, double_curly_brackets, exclude_keys=exclude_keys)
console.print("[bold white]Processed Prompt:[/bold white]")
console.print(processed)

# --- Selective include with select/mode attributes ---
# Extract only a specific function definition from a Python file:
selective_prompt = '<include select="def:preprocess" mode="interface">pdd/preprocess.py</include>'
console.print("\n[bold yellow]Selective include (function signature only):[/bold yellow]")
result = preprocess(selective_prompt, recursive=False, double_curly_brackets=False)
console.print(result)

# Extract by line range:
line_range_prompt = '<include select="lines:1-10">pdd/preprocess.py</include>'
console.print("\n[bold yellow]Selective include (lines 1-10):[/bold yellow]")
result = preprocess(line_range_prompt, recursive=False, double_curly_brackets=False)
console.print(result)

# --- Semantic LLM query include ---
# Uses IncludeQueryExtractor to ask an LLM about a file, with caching:
query_prompt = '<include query="What are the main public functions?">pdd/preprocess.py</include>'
console.print("\n[bold yellow]Semantic query include:[/bold yellow]")
result = preprocess(query_prompt, recursive=False, double_curly_brackets=False)
console.print(result)

# Semantic query is deferred during recursive pass:
console.print("\n[bold yellow]Semantic query (recursive=True, should be deferred):[/bold yellow]")
deferred = preprocess(query_prompt, recursive=True, double_curly_brackets=False)
console.print(deferred)  # Tag should remain intact

# --- include-many: multiple files concatenated ---
many_prompt = '<include-many>README.md, LICENSE</include-many>'
console.print("\n[bold yellow]Include-many:[/bold yellow]")
result = preprocess(many_prompt, recursive=False, double_curly_brackets=False)
console.print(result[:200] + "..." if len(result) > 200 else result)
