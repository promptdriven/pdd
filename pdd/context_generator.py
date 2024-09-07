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

def context_generator(
    code_module: str,
    prompt: str,
    language: str = "python",
    strength: float = 0.5,
    temperature: float = 0.0
) -> Tuple[str, float, str]:
    """
    Generates example code using a language model based on the provided prompt and parameters.

    Args:
        code_module (str): The code module to be used in generation.
        prompt (str): The input prompt for the language model.
        language (str, optional): The programming language for the output. Defaults to "python".
        strength (float, optional): The strength parameter for model selection. Defaults to 0.5.
        temperature (float, optional): The temperature parameter for model selection. Defaults to 0.0.

    Returns:
        Tuple[str, float, str]: The generated example code, total cost, and model name.
    """
    # Check for PDD_PATH environment variable
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    try:
        # Step 1: Load the example_generator prompt
        with open(f"{pdd_path}/prompts/example_generator_LLM.prompt", 'r') as file:
            example_generator_prompt = file.read()

        # Step 2: Preprocess the example_generator prompt
        preprocessed_prompt = preprocess(example_generator_prompt, recursive=False, double_curly_brackets=False)

        # Step 3: Create a Langchain LCEL template
        prompt_template = PromptTemplate.from_template(preprocessed_prompt)

        # Step 4: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 5: Preprocess the input prompt
        processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Step 6: Invoke the code through the model using Langchain LCEL
        chain = LLMChain(llm=llm, prompt=prompt_template)
        
        # Calculate and print token count and estimated cost
        total_tokens = token_counter(preprocessed_prompt + processed_prompt + code_module + language)
        estimated_cost = (total_tokens / 1_000_000) * input_cost
        print(f"[bold]Running generation with {total_tokens} tokens. Estimated input cost: ${estimated_cost:.6f}[/bold]")

        output = chain.run(code_module=code_module, processed_prompt=processed_prompt, language=language)

        # Step 7: Detect if the generation is incomplete
        last_600_chars = output[-600:]
        _, is_finished, unfinished_cost, _ = unfinished_prompt(last_600_chars, strength=0.5, temperature=temperature)

        if not is_finished:
            # Step 7a: Complete the generation
            output, continue_cost, _ = continue_generation(
                formatted_input_prompt=preprocessed_prompt,
                llm_output=output,
                strength=strength,
                temperature=temperature
            )
        else:
            continue_cost = 0

        # Step 7b: Postprocess the output
        example_code, postprocess_cost = postprocess(output, language, strength=0.9, temperature=temperature)

        # Step 8: Calculate and print total cost
        output_tokens = token_counter(output)
        total_cost = (
            estimated_cost +
            (output_tokens / 1_000_000) * output_cost +
            unfinished_cost +
            continue_cost +
            postprocess_cost
        )
        print(f"[bold green]Total cost: ${total_cost:.6f}[/bold green]")

        # Step 9: Return the results
        return example_code, total_cost, model_name

    except Exception as e:
        print(f"[bold red]Error in context_generator: {str(e)}[/bold red]")
        return "", 0.0, ""