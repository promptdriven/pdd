import os
from rich.console import Console
from rich.markdown import Markdown
from pdd.preprocess import preprocess
from pdd.llm_selector import llm_selector
from pdd.unfinished_prompt import unfinished_prompt
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser

console = Console()

def continue_generation(formatted_input_prompt: str, llm_output: str, strength: float, temperature: float):
    """
    Continues text generation using a language model, handling incomplete outputs and calculating costs.

    :param formatted_input_prompt: The input prompt formatted for the model.
    :param llm_output: The initial output from the language model.
    :param strength: The strength parameter for the LLM selector.
    :param temperature: The temperature parameter for the LLM selector.
    :return: The final output, total cost, and model name.
    """
    try:
        # Step 1: Load the continue_generation_LLM.prompt file
        pdd_path = os.getenv('PDD_PATH', '.')
        prompt_file_path = os.path.join(pdd_path, 'prompts', 'continue_generation_LLM.prompt')
        
        with open(prompt_file_path, 'r') as file:
            continue_generation_prompt = file.read()

        # Step 2: Preprocess the continue_generation prompt
        processed_prompt = preprocess(continue_generation_prompt, recursive=False, double_curly_brackets=False)
        
        # Step 3: Create a Langchain LCEL template
        prompt_template = PromptTemplate.from_template(processed_prompt)
        
        # Step 4: Use the llm_selector function
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)
        
        # Step 5: Run the input through the model
        chain = prompt_template | llm | StrOutputParser()
        result = chain.invoke({
            "FORMATTED_INPUT_PROMPT": formatted_input_prompt,
            "LLM_OUTPUT": llm_output
        })
        
        # Calculate token counts and costs
        input_token_count = token_counter(formatted_input_prompt)
        output_token_count = token_counter(result)
        total_cost = (input_token_count * input_cost + output_token_count * output_cost) / 1_000_000
        
        console.print(f"[bold white]Initial Output:[/bold white] {result}")
        console.print(f"[bold white]Input Token Count:[/bold white] {input_token_count}")
        console.print(f"[bold white]Output Token Count:[/bold white] {output_token_count}")
        console.print(f"[bold white]Estimated Cost:[/bold white] ${total_cost:.6f}")
        
        # Step 6: Detect if the generation is incomplete
        reasoning, is_finished, additional_cost, _ = unfinished_prompt(
            prompt_text=result,
            strength=.9,
            temperature=temperature
        )
        
        total_cost += additional_cost
        i = 0
        # Step 7: Loop if incomplete
        while not is_finished:
            print("********Loop: ", i)
            i += 1
            llm_output += result
            result = chain.invoke({
                "FORMATTED_INPUT_PROMPT": formatted_input_prompt,
                "LLM_OUTPUT": llm_output
            })
            
            output_token_count = token_counter(result)
            total_cost += (output_token_count * output_cost) / 1_000_000
            
            console.print(f"[bold white]Intermediate Output:[/bold white] {result}")
            console.print(f"[bold white]Output Token Count:[/bold white] {output_token_count}")
            console.print(f"[bold white]Estimated Cost:[/bold white] ${total_cost:.6f}")
            
            reasoning, is_finished, additional_cost, _ = unfinished_prompt(
                prompt_text=result,
                strength=.9,
                temperature=temperature
            )
            
            total_cost += additional_cost
        
        # Step 8: Pretty print the final output
        final_llm_output = llm_output + result
        console.print(Markdown(f"**Final Output:**\n{final_llm_output}"))
        console.print(f"[bold white]Total Token Count:[/bold white] {input_token_count + output_token_count}")
        console.print(f"[bold white]Total Cost:[/bold white] ${total_cost:.6f}")
        
        # Step 9: Return the final output, total cost, and model name
        return final_llm_output, total_cost, model_name
    
    except FileNotFoundError as e:
        console.print(f"[bold red]Error:[/bold red] {e}")
    except ValueError as e:
        console.print(f"[bold red]Error:[/bold red] {e}")
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred:[/bold red] {e}")
