from preprocess import preprocess
from rich.console import Console   
console = Console()     
prompt = """
<prompt>
    <include>example.txt</include>
    <shell>echo Hello World</shell>
    <pdd>This is a comment</pdd>
    ```<file_to_include.txt>```
</prompt>
"""
# load prompts/pdd_python.prompt
with open("prompts/pdd_python.prompt", "r") as file:
    prompt = file.read()

recursive = False
double_curly_brackets = True

processed = preprocess(prompt, recursive, double_curly_brackets)
console.print("[bold white]Processed Prompt:[/bold white]")
console.print(processed)
