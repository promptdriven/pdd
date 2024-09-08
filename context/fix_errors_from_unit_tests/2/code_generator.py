from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from . import preprocess
from . import llm_selector
from . import unfinished_prompt
from . import continue_generation
from . import postprocess

console = Console()

def code_generator(prompt: str, language: str, strength: float, temperature: float = 0.0) -> Tuple[str, float, str]:
    """
    Generates code based on the given prompt using a language model.

    Args:
    prompt (str): The raw prompt to be processed.
    language (str): The programming language of the output file.
    strength (float): The strength of the LLM model to use (between 0 and 1).
    temperature (float): The temperature of the LLM model to use. Default is 0.

    Returns:
    Tuple[str, float, str]: A tuple containing the runnable code, total cost, and model name.
    """
    model_name = ""  # Initialize model_name with a default value
    total_cost = 0.0  # Initialize total_cost
    try:
        # Step 1: Preprocess the raw prompt
        processed_prompt = preprocess.preprocess(prompt, recursive=True, double_curly_brackets=True)
        console.print(f"[bold]Processed prompt: {processed_prompt}[/bold]")

        # Step 2: Create a Langchain LCEL template
        prompt_template = PromptTemplate.from_template(processed_prompt)

        # Step 3: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector.llm_selector(strength, temperature)

        # Step 4: Run the prompt through the model
        chain = prompt_template | llm | (lambda x: x.content if hasattr(x, 'content') else str(x))
        token_count = token_counter(processed_prompt)
        input_token_cost = (token_count / 1_000_000) * input_cost

        console.print(f"[bold]Running prompt through {model_name}[/bold]")
        console.print(f"Input tokens: {token_count}")
        console.print(f"Estimated input cost: ${input_token_cost:.6f}")

        result = chain.invoke({})
        console.print(f"[bold]LLM result: {result}[/bold]")

        # Step 5: Pretty print the result and calculate output cost
        console.print(Markdown(result))
        output_token_count = token_counter(result)
        output_token_cost = (output_token_count / 1_000_000) * output_cost
        console.print(f"Output tokens: {output_token_count}")
        console.print(f"Estimated output cost: ${output_token_cost:.6f}")

        # Step 6: Detect if the generation is incomplete
        last_200_chars = result[-600:]
        _, is_finished, unfinished_cost, _ = unfinished_prompt.unfinished_prompt(last_200_chars, 0.5, temperature)

        if not is_finished:
            # Step 6a: Continue the generation if incomplete
            final_result, continue_cost, _ = continue_generation.continue_generation(processed_prompt, result, strength, temperature)
        else:
            # Step 6b: Postprocess if complete
            final_result, postprocess_cost = postprocess.postprocess(result, language, 0.9, temperature)

        # Step 7: Calculate and print total cost
        total_cost = input_token_cost + output_token_cost + (continue_cost if not is_finished else postprocess_cost) + unfinished_cost
        console.print(f"[bold]Total cost: ${total_cost:.6f}")

        # Step 8: Return the runnable code and total cost
        return final_result, total_cost, model_name

    except ValueError as e:
        console.print(f"[bold red]Value Error: {str(e)}[/bold red]")
        return "", total_cost, model_name
    except Exception as e:
        console.print(f"[bold red]Unexpected Error: {str(e)}[/bold red]")
        return "", total_cost, model_name