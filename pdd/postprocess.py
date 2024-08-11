import os
import json
import tiktoken
from rich import print as rprint
from rich.markdown import Markdown
from postprocess_0 import postprocess_0
from llm_selector import llm_selector
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.runnables import RunnablePassthrough

def postprocess(llm_output, language, strength=0.9, temperature=0):
    # Step 1: Use postprocess_0 if strength is 0
    if strength == 0:
        extracted_code = postprocess_0(llm_output, language)
        return extracted_code, 0.0

    # Step 2: Load the extract_code_LLM prompt
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise EnvironmentError("PDD_PATH environment variable is not set")
    
    prompt_path = os.path.join(pdd_path, 'prompts', 'extract_code_LLM.prompt')
    try:
        with open(prompt_path, 'r') as file:
            extract_code_prompt = file.read()
    except FileNotFoundError:
        raise FileNotFoundError(f"Prompt file not found at {prompt_path}")

    # Step 3: Create a Langchain LCEL template
    prompt_template = PromptTemplate.from_template(extract_code_prompt)
    parser = JsonOutputParser()

    # Step 4: Use llm_selector to get the LLM model
    llm, input_cost, output_cost = llm_selector(strength, temperature)

    # Step 5: Run the code through the model using Langchain LCEL
    chain = prompt_template | llm | parser

    # Prepare the input for the model
    input_data = {
        "llm_output": llm_output,
        "language": language
    }

    # Calculate token count using tiktoken
    encoding = tiktoken.get_encoding("cl100k_base")
    token_count = len(encoding.encode(json.dumps(input_data)))

    # Pretty print the running message
    rprint(f"Running model with {token_count} tokens. Estimated cost: ${input_cost * token_count / 1_000_000:.6f}")

    # Invoke the chain
    result = chain.invoke(input_data)

    # Step 5c: Access the 'extracted_code' key
    extracted_code = result.get('extracted_code', "Error: 'extracted_code' not found in the result")

    # Calculate output token count and total cost
    output_token_count = len(encoding.encode(extracted_code))
    total_cost = (input_cost * token_count + output_cost * output_token_count) / 1_000_000

    # Step 5d: Pretty print the extracted code
    rprint(Markdown(extracted_code))
    rprint(f"Output tokens: {output_token_count}, Output cost: ${output_cost * output_token_count / 1_000_000:.6f}, Total cost: ${total_cost:.6f}")

    # Step 6: Return the extracted code and total cost
    return extracted_code, total_cost