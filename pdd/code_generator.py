# To implement the `code_generator` function as described, we will follow the steps outlined in your prompt. The function will preprocess the prompt, create a Langchain LCEL template, run the model, and then postprocess the output to return runnable code. We will also use the `rich` library for pretty printing.

# Here's how the implementation looks:

# ```python
import os
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from preprocess import preprocess
from postprocess import postprocess
import tiktoken

console = Console()

def code_generator(prompt: str, file_type: str) -> str:
    # Step 1: Preprocess the raw prompt
    try:
        processed_prompt = preprocess(prompt)
        console.print(f"[bold green]Preprocessed prompt successfully.[/bold green]")
    except FileNotFoundError as e:
        console.print(f"[bold red]Error: {e}[/bold red]")
        return ""

    # Step 2: Create a Langchain LCEL template
    prompt_template = PromptTemplate.from_template(processed_prompt)
    
    # Step 3: Initialize the model
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)

    # Step 4: Count tokens in the prompt
    encoding = tiktoken.get_encoding("cl100k_base")
    token_count = len(encoding.encode(processed_prompt))
    console.print(f"[bold blue]Running the model with {token_count} tokens...[/bold blue]")

    # Combine with a model and parser to output a string
    chain = prompt_template | llm | StrOutputParser()

    # Run the template
    result = chain.invoke({})
    
    # Step 5: Pretty print the markdown result
    console.print(Markdown(result))
    result_token_count = len(encoding.encode(result))
    console.print(f"[bold blue]Result contains {result_token_count} tokens.[/bold blue]")

    # Step 6: Postprocess the model output
    runnable_code = postprocess(result, file_type)

    # Step 7: Return the runnable code
    return runnable_code
# ```

# ### Explanation of the Code:
# 1. **Imports**: We import necessary modules including `rich` for pretty printing, Langchain components for prompt handling, and the `preprocess` and `postprocess` functions.
# 2. **Console Initialization**: We create a `Console` object from the `rich` library to handle pretty printing.
# 3. **Function Definition**: The `code_generator` function takes a `prompt` (file path) and `file_type` (e.g., "python").
# 4. **Preprocessing**: We attempt to preprocess the prompt. If the file is not found, we print an error message and return an empty string.
# 5. **Prompt Template Creation**: We create a prompt template using the processed prompt.
# 6. **Model Initialization**: We initialize the `ChatOpenAI` model with specified parameters.
# 7. **Token Counting**: We count the tokens in the processed prompt and print the count.
# 8. **Model Invocation**: We run the prompt through the model and capture the result.
# 9. **Markdown Printing**: We pretty print the result using the `Markdown` function from `rich`.
# 10. **Postprocessing**: We call the `postprocess` function to format the output into runnable code.
# 11. **Return**: Finally, we return the runnable code.

# ### Usage:
# To use this function, you would call it with the path to your prompt file and the desired output file type. For example:

# ```python
# runnable_code = code_generator('path/to/prompt.txt', 'python')
# print(runnable_code)
# ```

# Make sure to have the necessary modules installed and available in your environment for this code to run successfully.