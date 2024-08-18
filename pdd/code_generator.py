# To achieve the desired functionality, we will create a Python function named `code_generator` that follows the steps outlined. This function will use Langchain to process a prompt, select an appropriate LLM model, run the prompt through the model, and postprocess the result to generate runnable code. We'll also use the `rich` library for pretty printing.

# Here's the complete implementation:

# ```python
import os
from rich import print
from rich.markdown import Markdown
from preprocess import preprocess
from llm_selector import llm_selector
from postprocess import postprocess
import tiktoken
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from langchain.globals import set_llm_cache
from langchain_community.cache import SQLiteCache
from langchain_core.pydantic_v1 import BaseModel, Field

# Setup cache to save money and increase speeds
set_llm_cache(SQLiteCache(database_path=".langchain.db"))

def code_generator(prompt: str, file_type: str, strength: float) -> str:
    # Step 1: Preprocess the raw prompt
    try:
        processed_prompt = preprocess(prompt)
    except FileNotFoundError as e:
        print(f"[bold red]Error:[/bold red] {e}")
        return ""

    # Step 2: Create a Langchain LCEL template from the processed prompt
    prompt_template = PromptTemplate.from_template(processed_prompt)

    # Step 3: Use llm_selector and a temperature of 0 for the model
    temperature = 0
    llm, token_counter, input_cost, output_cost = llm_selector(strength, temperature)

    # Step 4: Run the prompt through the model using Langchain LCEL
    chain = prompt_template | llm | StrOutputParser()

    # Calculate token count using tiktoken
    encoding = tiktoken.get_encoding("cl100k_base")
    token_count = len(encoding.encode(processed_prompt))
    cost = (token_count / 1_000_000) * input_cost

    print(f"[bold green]Running the model...[/bold green]")
    print(f"Token count in prompt: {token_count}")
    print(f"Estimated cost: ${cost:.6f}")

    result = chain.invoke({})

    # Step 5: Pretty print the markdown formatting in the result
    print(Markdown(result))
    result_token_count = len(encoding.encode(result))
    result_cost = (result_token_count / 1_000_000) * output_cost
    total_cost = cost + result_cost

    print(f"Token count in result: {result_token_count}")
    print(f"Result cost: ${result_cost:.6f}")
    print(f"Total cost: ${total_cost:.6f}")

    # Step 6: Postprocess the model output to create runnable code
    runnable_code, total_cost = postprocess(result, file_type)

    # Step 7: Return the runnable code
    return runnable_code

# Example usage
if __name__ == "__main__":
    prompt_path = "path/to/your/prompt.txt"
    file_type = "python"
    strength = 0.8

    code = code_generator(prompt_path, file_type, strength)
    print(f"[bold blue]Generated Code:[/bold blue]\n{code}")
# ```

# ### Explanation:
# 1. **Preprocess the Prompt**: The `preprocess` function is used to preprocess the raw prompt from the file.
# 2. **Create LCEL Template**: A Langchain LCEL template is created from the processed prompt.
# 3. **Select LLM Model**: The `llm_selector` function is used to select an appropriate LLM model based on the given strength and a fixed temperature of 0.
# 4. **Run the Model**: The prompt is run through the model using Langchain LCEL. The token count and estimated cost are calculated and printed.
# 5. **Pretty Print Result**: The result is pretty printed using the `rich` library's `Markdown` function. The token count and cost of the result are also printed.
# 6. **Postprocess the Result**: The result is postprocessed to create runnable code.
# 7. **Return Runnable Code**: The runnable code is returned.

# This function integrates all the required steps and uses the `rich` library for pretty printing, ensuring that the output is user-friendly and informative.