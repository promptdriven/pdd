# Certainly! I'll create a Python function `test_generator` that follows the steps you've outlined. Here's the implementation:

# ```python
import os
import sys
from pathlib import Path
import tiktoken
from rich import print
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from llm_selector import llm_selector
from postprocess import postprocess

def test_generator(prompt_file: str, code_file: str, strength: float, language: str, test_directory: str) -> str:
    # Step 1: Load necessary files
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    test_generator_prompt_path = Path(pdd_path) / 'prompts' / 'test_generator_LLM.prompt'
    with open(test_generator_prompt_path, 'r') as f:
        test_generator_prompt = f.read()

    with open(prompt_file, 'r') as f:
        prompt_that_generated_code = f.read()

    with open(code_file, 'r') as f:
        code = f.read()

    # Step 2: Create Langchain LCEL template
    prompt_template = PromptTemplate.from_template(test_generator_prompt)

    # Step 3: Use llm_selector
    llm, input_cost, output_cost = llm_selector(strength, temperature=0)

    # Step 4: Run the code through the model
    chain = prompt_template | llm | StrOutputParser()

    # Calculate token count and cost
    encoding = tiktoken.get_encoding("cl100k_base")
    prompt_tokens = len(encoding.encode(test_generator_prompt))
    prompt_cost = (input_cost / 1_000_000) * prompt_tokens

    print(f"[bold green]Running the model...[/bold green]")
    print(f"Prompt tokens: {prompt_tokens}")
    print(f"Estimated prompt cost: ${prompt_cost:.6f}")

    result = chain.invoke({
        "prompt_that_generated_code": prompt_that_generated_code,
        "code": code,
        "test_directory": test_directory,
        "language": language,
        "code_directory": os.path.dirname(code_file)
    })

    # Step 5: Pretty print the result and calculate costs
    print(Markdown(result))

    result_tokens = len(encoding.encode(result))
    result_cost = (output_cost / 1_000_000) * result_tokens
    total_cost = prompt_cost + result_cost

    print(f"Result tokens: {result_tokens}")
    print(f"Estimated result cost: ${result_cost:.6f}")
    print(f"[bold]Total estimated cost: ${total_cost:.6f}[/bold]")

    # Step 6: Postprocess the result
    processed_result = postprocess(result, language)

    # Step 7: Return the unit test code
    return processed_result

# Example usage:
if __name__ == "__main__":
    prompt_file = "path/to/prompt_file.txt"
    code_file = "path/to/code_file.py"
    strength = 0.7
    language = "python"
    test_directory = "path/to/test/directory"

    unit_test_code = test_generator(prompt_file, code_file, strength, language, test_directory)
    print("[bold blue]Generated Unit Test Code:[/bold blue]")
    print(unit_test_code)
# ```

# This implementation follows all the steps you've outlined:

# 1. It loads the necessary files using the `PDD_PATH` environment variable.
# 2. It creates a Langchain LCEL template from the test generator prompt.
# 3. It uses the `llm_selector` function with a temperature of 0.
# 4. It runs the loaded code file through the model using Langchain LCEL, passing all required parameters.
# 5. It pretty prints the markdown formatting in the result an