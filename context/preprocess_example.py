from pdd.preprocess import preprocess
from rich.console import Console   
console = Console()     
prompt = """
<prompt>
    <include>Makefile</include>
    <shell>echo Hello World</shell>
    <pdd>This is a comment</pdd>
    <web>https://python.langchain.com/docs/introduction/</web>
    {test}
    {test2}
    ```<TODO.md>```
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

# Debug test without the include tag to see if that's causing the issue
console.print("\n[bold magenta]Testing without include tag:[/bold magenta]")
test_prompt = """
<prompt>
    <shell>echo Hello World</shell>
    <pdd>This is a comment</pdd>
    <web>https://python.langchain.com/docs/introduction/</web>
    {test}
    {test2}
    ```<TODO.md>```
</prompt>
"""
test_processed = preprocess(test_prompt, recursive, double_curly_brackets, exclude_keys=exclude_keys)
console.print(test_processed)

# Bare minimum test
console.print("\n[bold magenta]Bare minimum test:[/bold magenta]")
simple_prompt = """
<prompt>
    {test}
    {test2}
</prompt>
"""
simple_processed = preprocess(simple_prompt, recursive, double_curly_brackets, exclude_keys=exclude_keys)
console.print(simple_processed)

# load prompts/change_LLM.prompt
# with open('prompts/xml/change_LLM.prompt', 'r') as file:
#     change_LLM_prompt = file.read()
    
# # call preprocess on change_LLM_prompt
# processed = preprocess(change_LLM_prompt, recursive, False)
# console.print("[bold white]Processed change_LLM Prompt:[/bold white]")
# console.print(processed)

# # write the processed prompt to a file
# with open('tests/preprocess_test_change_example_full_complete.prompt', 'w') as file:
#     file.write(processed)
    

# with open('prompts/example_generator_LLM.prompt', 'r') as file:
#     example_generator_LLM_prompt = file.read()
    
# # call preprocess on change_LLM_prompt
# processed = preprocess(example_generator_LLM_prompt, recursive, False)
# console.print("[bold white]Processed change_LLM Prompt:[/bold white]")
# console.print(processed)

# # write the processed prompt to a file
# with open('tests/preprocess_test_example_generator_LLM.prompt', 'w') as file:
#     file.write(processed)

# prompt = """    mock_db = {
#         "1": {"id": "1", "name": "Resource One"},
#         "2": {"id": "2", "name": "Resource Two"}
#     }"""

# processed = preprocess(prompt, recursive, True)
# console.print("[bold white]Processed change_LLM Prompt:[/bold white]")
# console.print(processed)