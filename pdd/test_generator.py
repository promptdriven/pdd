# Certainly! I'll create a Python function `test_generator` that follows the steps you've outlined. Here's the implementation:

# ```python
import os
from pathlib import Path
import tiktoken
from rich import print
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from llm_selector import llm_selector
from postprocess import postprocess

def test_generator(prompt_file: str, code_file: str, strength: float, language: str, test_directory: str) -> str:
    # Step 1: Load prompt and code files
    pdd_path = os.environ.get('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    prompt_path = Path(pdd_path) / 'prompts' / 'test_generator_LLM.prompt'
    with open(prompt_path, 'r') as f:
        prompt_template = f.read()

    with open(code_file, 'r') as f:
        code_content = f.read()

    # Step 2: Create Langchain LCEL template
    prompt = PromptTemplate.from_template(prompt_template)

    # Step 3: Use llm_selector with temperature 0
    llm, input_cost, output_cost = llm_selector(strength, temperature=0)

    # Step 4: Run the code through the model
    chain = prompt | llm | StrOutputParser()

    # Calculate token count and cost
    encoding = tiktoken.get_encoding("cl100k_base")
    prompt_tokens = len(encoding.encode(prompt_template))
    code_tokens = len(encoding.encode(code_content))
    total_input_tokens = prompt_tokens + code_tokens
    input_cost_estimate = (total_input_tokens / 1_000_000) * input_cost

    print(Markdown(f"## Running Test Generator"))
    print(f"Input tokens: {total_input_tokens}")
    print(f"Estimated input cost: ${input_cost_estimate:.6f}")

    # Invoke the chain
    result = chain.invoke({
        "prompt_that_generated_code": prompt_file,
        "code": code_content,
        "test_directory": test_directory,
        "language": language,
        "code_directory": os.path.dirname(code_file)
    })

    # Step 5: Pretty print the result and calculate output cost
    print(Markdown("## Generated Test"))
    print(Markdown(result))

    result_tokens = len(encoding.encode(result))
    output_cost_estimate = (result_tokens / 1_000_000) * output_cost
    total_cost = input_cost_estimate + output_cost_estimate

    print(f"Output tokens: {result_tokens}")
    print(f"Estimated output cost: ${output_cost_estimate:.6f}")
    print(f"Total estimated cost: ${total_cost:.6f}")

    # Step 6: Postprocess the result
    processed_result = postprocess(result, language)

    # Step 7: Return the unit test code
    return processed_result

# Example usage:
# test_code = test_generator(
#     prompt_file="path/to/prompt_file",
#     code_file="path/to/code_file",
#     strength=0.7,
#     language="python",
#     test_directory="path/to/test/directory"
# )
# print(test_code)
# ```

# This implementation follows all the steps you've outlined:

# 1. It loads the prompt template and code file using the `PDD_PATH` environment variable.
# 2. It creates a Langchain LCEL template from the loaded prompt.
# 3. It uses the `llm_selector` function with the given strength and a temperature of 0.
# 4. It runs the code through the model, passing all required parameters. It also calculates and displays the input token count and estimated cost.
# 5. It pretty prints the markdown formatting in the result using Rich's Markdown function, and calculates and displays the output token count, cost, and total cost.
# 6. It uses the `