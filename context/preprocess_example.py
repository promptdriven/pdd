from pdd.preprocess import preprocess
from rich.console import Console   
console = Console()     
prompt = """
<prompt>
    <include>Makefile</include>
    <shell>echo Hello World</shell>
    <pdd>This is a comment</pdd>
    ```<TODO.md>```
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
with open('tests/preprocess_test_change_example_full_complete.prompt', 'w') as file:
    file.write(processed)
    

with open('prompts/example_generator_LLM.prompt', 'r') as file:
    example_generator_LLM_prompt = file.read()
    
# call preprocess on change_LLM_prompt
processed = preprocess(example_generator_LLM_prompt, recursive, False)
console.print("[bold white]Processed change_LLM Prompt:[/bold white]")
console.print(processed)

# write the processed prompt to a file
with open('tests/preprocess_test_example_generator_LLM.prompt', 'w') as file:
    file.write(processed)

prompt = """    mock_db = {
        "1": {"id": "1", "name": "Resource One"},
        "2": {"id": "2", "name": "Resource Two"}
    }"""
processed = preprocess(prompt, recursive, True)
console.print("[bold white]Processed change_LLM Prompt:[/bold white]")
console.print(processed)