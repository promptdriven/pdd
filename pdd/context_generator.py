import os
from typing import Tuple
from rich import print
from .preprocess import preprocess
from .llm_selector import llm_selector
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess
from langchain.prompts import PromptTemplate
from langchain.chains import LLMChain

def context_generator(code_module: str, prompt: str, language: str = "python", strength: float = 0.5, temperature: float = 0.0) -> Tuple[str, float, str]:
    """
    Generates example code using a language model based on the provided code module and prompt.

    :param code_module: The code module to be used in the generation process.
    :param prompt: The input prompt for the language model.
    :param language: The programming language for the generated code.
    :param strength: The strength parameter for model selection.
    :param temperature: The temperature parameter for model selection.
    :return: A tuple containing the generated example code, the total cost, and the model name.
    """
    try:
        # Step 1: Load the example_generator prompt
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")
        
        with open(f"{pdd_path}/prompts/example_generator_LLM.prompt", 'r') as file:
            example_generator_prompt = file.read()

        # Step 2: Preprocess the example_generator prompt
        preprocessed_prompt = preprocess(example_generator_prompt, recursive=False, double_curly_brackets=False)

        # Step 3: Create a Langchain LCEL template
        prompt_template = PromptTemplate(template=preprocessed_prompt, input_variables=["code_module", "processed_prompt", "language"])

        # Step 4: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 5: Preprocess the input prompt
        processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Step 6: Invoke the code through the model using Langchain LCEL
        chain = LLMChain(llm=llm, prompt=prompt_template)
        
        # Calculate and print token count and estimated cost
        total_tokens = token_counter(preprocessed_prompt) + token_counter(processed_prompt) + token_counter(code_module) + token_counter(language)
        estimated_cost = (total_tokens / 1_000_000) * input_cost
        print(f"[bold]Running example generation...[/bold]")
        print(f"Total input tokens: {total_tokens}")
        print(f"Estimated input cost: ${estimated_cost:.6f}")

        # Invoke the chain
        result = chain.run(code_module=code_module, processed_prompt=processed_prompt, language=language)

        # Step 7: Detect if the generation is incomplete
        last_600_chars = result[-600:]
        _, is_finished, unfinished_cost, _ = unfinished_prompt(last_600_chars, strength=0.5, temperature=temperature)

        if not is_finished:
            # Step 7a: If incomplete, continue the generation
            result, continue_cost, _ = continue_generation(preprocessed_prompt, result, strength, temperature)
        else:
            continue_cost = 0

        # Step 7b: If complete, postprocess the result
        example_code, postprocess_cost = postprocess(result, language, strength=0.9, temperature=temperature)

        # Step 8: Calculate and print the total cost
        output_tokens = token_counter(example_code)
        output_cost_value = (output_tokens / 1_000_000) * output_cost
        total_cost = estimated_cost + output_cost_value + unfinished_cost + continue_cost + postprocess_cost

        print(f"[bold]Generation complete![/bold]")
        print(f"Total output tokens: {output_tokens}")
        print(f"Total cost: ${total_cost:.6f}")

        # Step 9: Return the results
        return example_code, total_cost, model_name

    except Exception as e:
        print(f"[bold red]Error in context_generator: {str(e)}[/bold red]")
        return "", 0.0, ""
