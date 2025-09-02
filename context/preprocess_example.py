from pdd.preprocess import preprocess
from rich.console import Console   
console = Console()     

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
