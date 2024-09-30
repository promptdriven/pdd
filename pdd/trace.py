import os
from langchain import LLM
from langchain.prompts import load_prompt
from langchain.token_counter import token_counter
from langchain.llm_selector import llm_selector
from langchain.utils import preprocess

def context_generator(code_file: str, code_line: int, prompt_file: str, language: str = "python", strength: float = 0.5, temperature: float = 0) -> tuple:
    """
    Generates context by processing code and prompt files, invoking a language model, and calculating costs.

    :param code_file: The code file content as a string.
    :param code_line: The line number in the code file to extract.
    :param prompt_file: The prompt file content as a string.
    :param language: The programming language of the code.
    :param strength: The strength parameter for model selection.
    :param temperature: The temperature parameter for model selection.
    :return: A tuple containing the prompt line number, total cost, and model name.
    """
    # Step 1: Load the prompt file
    pdd_path = os.getenv('PDD_PATH')
    trace_prompt_path = os.path.join(pdd_path, 'prompts', 'trace_LLM.prompt')
    with open(trace_prompt_path, 'r') as f:
        trace_prompt = f.read()
    
    # Step 2: Find the substring of the code_file that matches the code_line
    code_lines = code_file.splitlines()
    code_str = code_lines[code_line - 1] if 0 < code_line <= len(code_lines) else ""
    
    # Step 3: Preprocess the loaded trace_LLM prompt
    processed_trace_prompt = preprocess(trace_prompt, recursive=False, double_curly_brackets=False)
    
    # Step 4: Create a Langchain LCEL template from the preprocessed trace_LLM prompt
    trace_template = LLM.create_template(processed_trace_prompt)
    
    # Step 5: Use llm_selector for the model
    model_name = llm_selector(language, strength, temperature)
    
    # Step 6: Preprocess the prompt_file
    processed_prompt = preprocess(prompt_file, recursive=False, double_curly_brackets=False)
    
    # Step 7: Invoke the code through the model using Langchain LCEL
    print(f"Running model '{model_name}' with prompt containing {token_counter(processed_trace_prompt)} tokens.")
    llm_output = trace_template.invoke({
        'CODE_FILE': code_file,
        'CODE_STR': code_str,
        'PROMPT_FILE': processed_prompt
    })
    
    # Step 8: Load the extract_promptline_LLM prompt
    extract_promptline_path = os.path.join(pdd_path, 'prompts', 'extract_promptline_LLM.prompt')
    with open(extract_promptline_path, 'r') as f:
        extract_promptline = f.read()
    
    # Step 9: Preprocess the loaded extract_promptline_LLM prompt
    processed_extract_promptline = preprocess(extract_promptline, recursive=False, double_curly_brackets=False)
    
    # Step 10: Create a Langchain LCEL template from the preprocessed extract_promptline_LLM prompt
    extract_template = LLM.create_template(processed_extract_promptline)
    
    # Step 11: Use llm_selector for the model
    model_name = llm_selector(language, strength, temperature)
    
    # Step 12: Invoke the code through the model using Langchain LCEL
    print(f"Running model '{model_name}' with prompt containing {token_counter(processed_extract_promptline)} tokens.")
    prompt_line_output = extract_template.invoke({
        'llm_output': llm_output
    })
    
    # Step 13: Find the line of the prompt_file that matches the prompt_line as an integer
    prompt_line = int(prompt_line_output.strip())
    
    # Step 14: Calculate total cost (assuming cost is calculated based on tokens)
    total_cost = (token_counter(processed_trace_prompt) + token_counter(processed_extract_promptline)) * 0.000001  # Cost per million tokens
    
    return prompt_line, total_cost, model_name
