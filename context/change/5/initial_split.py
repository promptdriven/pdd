#To implement the `split` function as described, we need to follow a structured approach using the Langchain library, the `llm_selector` function, and the `tiktoken` library for token counting. Additionally, we'll use the `rich` library for pretty printing. Below is a step-by-step implementation of the function:
#
#```python
import os
import json
from rich import print as rprint
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser
from langchain_openai import ChatOpenAI
from llm_selector import llm_selector
import tiktoken

# Define the function
def split(input_prompt, input_code, example_code, strength, temperature):
    # Step 1: Load the prompt files
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    split_llm_prompt_path = os.path.join(pdd_path, 'prompts/xml', 'split_xml_LLM.prompt')
    extract_prompt_split_llm_prompt_path = os.path.join(pdd_path, 'prompts', 'extract_prompt_split_LLM.prompt')

    with open(split_llm_prompt_path, 'r') as file:
        split_llm_prompt = file.read()

    with open(extract_prompt_split_llm_prompt_path, 'r') as file:
        extract_prompt_split_llm_prompt = file.read()

    # Step 2: Create Langchain LCEL template for split_LLM
    split_prompt_template = PromptTemplate.from_template(split_llm_prompt)

    # Step 3: Use llm_selector to get the LLM model
    llm, input_cost, output_cost = llm_selector(strength, temperature)

    # Step 4: Run the input through the model using Langchain LCEL
    chain = split_prompt_template | llm | StrOutputParser()
    input_data = {
        "input_prompt": input_prompt,
        "input_code": input_code,
        "example_code": example_code
    }
    llm_output = chain.invoke(input_data)

    # Calculate token count and cost
    encoding = tiktoken.get_encoding("cl100k_base")
    input_tokens = len(encoding.encode(json.dumps(input_data)))
    output_tokens = len(encoding.encode(llm_output))
    total_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000

    rprint(f"[bold green]Running model...[/bold green]")
    rprint(f"Input Tokens: {input_tokens}, Output Tokens: {output_tokens}, Estimated Cost: ${total_cost:.6f}")

    # Step 5: Create Langchain LCEL template for extract_prompt_split_LLM
    extract_prompt_template = PromptTemplate.from_template(extract_prompt_split_llm_prompt)
    parser = JsonOutputParser()

    chain = extract_prompt_template | llm | parser
    result = chain.invoke({"llm_output": llm_output})

    # Calculate token count and cost for extraction
    extract_input_tokens = len(encoding.encode(llm_output))
    extract_output_tokens = len(encoding.encode(json.dumps(result)))
    extract_cost = (extract_input_tokens * input_cost + extract_output_tokens * output_cost) / 1_000_000

    rprint(f"[bold green]Extracting prompts...[/bold green]")
    rprint(f"Input Tokens: {extract_input_tokens}, Output Tokens: {extract_output_tokens}, Estimated Cost: ${extract_cost:.6f}")

    # Step 6: Pretty print the extracted sub_prompt and modified_prompt
    sub_prompt = result.get('sub_prompt', '')
    modified_prompt = result.get('modified_prompt', '')

    rprint(Markdown(f"**Sub Prompt:**\n{sub_prompt}"))
    rprint(Markdown(f"**Modified Prompt:**\n{modified_prompt}"))

    # Step 7: Return the sub_prompt, modified_prompt, and total_cost
    return sub_prompt, modified_prompt, total_cost + extract_cost

# Example usage
# sub_prompt, modified_prompt, total_cost = split("input_prompt", "input_code", "example_code", 0.5, 0.7)
# rprint(f"Sub Prompt: {sub_prompt}, Modified Prompt: {modified_prompt}, Total Cost: {total_cost}")
#```
#
#### Explanation:
#1. **Environment Variables**: The function checks for the `PDD_PATH` environment variable to locate the prompt files.
#2. **Prompt Loading**: It reads the prompt templates from the specified files.
#3. **Langchain Setup**: It sets up the Langchain LCEL templates and chains them with the selected LLM model.
#4. **Token Counting**: It uses `tiktoken` to count tokens and calculate costs based on the input and output token counts.
#5. **Rich Printing**: It uses the `rich` library to pretty print the process and results.
#6. **Error Handling**: The function raises an error if the necessary environment variables are not set.
#
#This implementation assumes that the `llm_selector` function and the `tiktoken` library are correctly set up and available in your environment. Adjust paths and configurations as necessary for your specific setup.