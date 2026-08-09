import os
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
import tiktoken
from preprocess import preprocess
from llm_selector import llm_selector
from postprocess import postprocess

console = Console()

def test_generator(prompt: str, code: str, strength: float, temperature: float, language: str) -> tuple[str, float]:
    """
    Generates a unit test based on the provided prompt and code.

    :param prompt: The prompt that describes the task.
    :param code: The code for which the unit test is to be generated.
    :param strength: The strength parameter for model selection.
    :param temperature: The temperature parameter for model selection.
    :param language: The programming language of the code.
    :return: A tuple containing the generated unit test and the total cost.
    """
    try:
        # Step 1: Load the prompt file
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise EnvironmentError("PDD_PATH environment variable is not set.")
        with open(f'{pdd_path}/prompts/test_generator_LLM.prompt', 'r') as file:
            prompt_template = file.read()

        # Step 2: Preprocess the prompt
        processed_prompt = preprocess(prompt_template, recursive=False, double_curly_brackets=False)

        # Create Langchain LCEL template
        lcel_template = PromptTemplate.from_template(processed_prompt)

        # Step 3: Use llm_selector for the model
        llm, input_cost, output_cost = llm_selector(strength, temperature)

        # Step 4: Run inputs through the model using Langchain LCEL
        chain = lcel_template | llm | StrOutputParser()

        # Calculate token count and cost
        encoding = tiktoken.get_encoding("cl100k_base")
        input_tokens = len(encoding.encode(processed_prompt + prompt + code + language))
        input_cost_estimate = (input_tokens / 1_000_000) * input_cost

        console.print(f"[bold]Running model with {input_tokens} input tokens[/bold]")
        console.print(f"[bold]Estimated input cost: ${input_cost_estimate:.6f}[/bold]")

        # Invoke the chain
        result = chain.invoke({
            "prompt_that_generated_code": prompt,
            "code": code,
            "language": language
        })

        # Step 5: Pretty print the result
        console.print(Markdown(result))

        # Calculate output tokens and cost
        output_tokens = len(encoding.encode(result))
        output_cost_estimate = (output_tokens / 1_000_000) * output_cost

        console.print(f"[bold]Output tokens: {output_tokens}[/bold]")
        console.print(f"[bold]Estimated output cost: ${output_cost_estimate:.6f}[/bold]")

        # Step 6: Postprocess the result
        unit_test, postprocess_cost = postprocess(result, language, strength, temperature)
        console.print(f"[bold]Postprocess cost: ${postprocess_cost:.6f}[/bold]")

        # Calculate total cost
        total_cost = input_cost_estimate + output_cost_estimate + postprocess_cost
        console.print(f"[bold]Total cost: ${total_cost:.6f}[/bold]")

        # Step 7: Return the unit test code and total cost
        return unit_test, total_cost

    except Exception as e:
        console.print(f"[bold red]An error occurred: {e}[/bold red]")
        return "", 0.0