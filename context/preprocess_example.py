from preprocess import preprocess
from rich.console import Console   
console = Console()     
prompt = """
<prompt>
    <include>example.txt</include>
    <shell>echo Hello World</shell>
    <pdd>This is a comment</pdd>
    ``` <file_to_include.txt>```
</prompt>
"""

recursive = False
double_curly_brackets = True

processed = preprocess(prompt, recursive, double_curly_brackets)
console.print("[bold white]Processed Prompt:[/bold white]")
console.print(processed)

# load prompts/change_LLM.prompt
with open('prompts/xml/change_LLM.prompt', 'r') as file:
    change_LLM_prompt = file.read()
    
# call preprocess on change_LLM_prompt
processed = preprocess(change_LLM_prompt, recursive, False)
console.print("[bold white]Processed change_LLM Prompt:[/bold white]")
console.print(processed)

# write the processed prompt to a file
with open('prompts/xml/change_LLM_processed.prompt', 'w') as file:
    file.write(processed)