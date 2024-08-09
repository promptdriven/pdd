# To achieve the goal of splitting a prompt into a `sub_prompt` and `modified_prompt` using Langchain and other tools, we need to follow the steps outlined in the prompt. Below is the implementation of the `split_prompt` function, which includes error handling and pretty printing using the `rich` library.

# First, ensure you have the necessary libraries installed:
# ```bash
# pip install langchain rich tiktoken
# ```

# Now, let's implement the `split_prompt` function:

# ```python
import os
from rich import print
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_google_genai import ChatGoogleGenerativeAI
from langchain_anthropic import ChatAnthropic
from langchain_community.cache import SQLiteCache
from langchain.globals import set_llm_cache
from langchain_core.pydantic_v1 import BaseModel, Field
from langchain.output_parsers import RetryOutputParser
import tiktoken

# Define the function
def split_prompt(input_prompt, input_code, example_code, strength):
    console = Console()
    
    try:
        # Step 1: Load the prompt files
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set.")
        
        split_llm_prompt_path = os.path.join(pdd_path, 'prompts', 'split_LLM.prompt')
        extract_prompt_split_llm_path = os.path.join(pdd_path, 'prompts', 'extract_prompt_split_LLM.prompt')
        
        with open(split_llm_prompt_path, 'r') as file:
            split_llm_prompt = file.read()
        
        with open(extract_prompt_split_llm_path, 'r') as file:
            extract_prompt_split_llm = file.read()
        
        # Step 2: Create Langchain LCEL template from the split_LLM prompt
        prompt_template = PromptTemplate.from_template(split_llm_prompt)
        
        # Step 3: Use llm_selector and a temperature of 0 for the llm model
        from llm_selector import llm_selector
        llm, input_cost, output_cost = llm_selector(strength, 0)
        
        # Step 4: Run the code through the model using Langchain LCEL
        chain = prompt_template | llm | StrOutputParser()
        
        # Prepare the input for the prompt
        prompt_input = {
            "input_prompt": input_prompt,
            "input_code": input_code,
            "example_code": example_code
        }
        
        # Calculate token count and cost
        encoding = tiktoken.get_encoding("cl100k_base")
        token_count = len(encoding.encode(str(prompt_input)))
        cost = (token_count / 1_000_000) * input_cost
        
        # Pretty print the running message
        console.print(f"[bold green]Running the model...[/bold green]")
        console.print(f"Token count: {token_count}")
        console.print(f"Estimated cost: ${cost:.6f}")
        
        # Invoke the chain
        result = chain.invoke(prompt_input)
        
        # Pretty print the result
        console.print(Markdown(result))
        result_token_count = len(encoding.encode(result))
        result_cost = (result_token_count / 1_000_000) * output_cost
        console.print(f"Result token count: {result_token_count}")
        console.print(f"Result cost: ${result_cost:.6f}")
        
        # Step 6: Create a second Langchain LCEL template from extract_prompt_split_LLM
        extract_prompt_template = PromptTemplate.from_template(extract_prompt_split_llm)
        extract_chain = extract_prompt_template | llm | JsonOutputParser()
        
        # Invoke the chain to extract sub_prompt and modified_prompt
        extract_result = extract_chain.invoke(result)
        
        # Pretty print the total cost
        total_cost = cost + result_cost
        console.print(f"Total cost: ${total_cost:.6f}")
        
        return extract_result['sub_prompt'], extract_result['modified_prompt']
    
    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {e}")
        return None, None

# Example usage
input_prompt = "Your input prompt here"
input_code = "Your input code here"
example_code = "Your example code here"
strength = 0.5

sub_prompt, modified_prompt = split_prompt(input_prompt, input_code, example_code, strength)
print(f"Sub Prompt: {sub_prompt}")
print(f"Modified Prompt: {modified_prompt}")
# ```

# ### Explanation:
# 1. **Environment Variable**: The function checks for the `PDD_PATH` environment variable and loads the necessary prompt files.
# 2. **Prompt Templates**: It creates Langchain LCEL templates from the loaded prompts.
# 3. **LLM Selection**: It uses the `llm_selector` function to select the appropriate LLM model based on the provided strength.
# 4. **Token Calculation**: It calculates the number of tokens in the input and estimates the cost using `tiktoken`.
# 5. **Model Invocation**: It runs the model and pretty prints the result using `rich`.
# 6. **Extraction**: It uses another Langchain LCEL template to extract the `sub_prompt` and `modified_prompt`.
# 7. **Error Handling**: It handles potential errors gracefully and prints error messages using `rich`.

# This function should be able to split the prompt as required and provide detailed output and cost information.