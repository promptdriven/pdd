from typing import Tuple
from rich import print
from pydantic import BaseModel, Field
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import DEFAULT_TIME, DEFAULT_STRENGTH

def _apply_language_specific_fixes(code: str, language: str, verbose: bool = False) -> str:
    """
    Apply language-specific fixes to generated code.
    
    This function provides a clean, extensible way to add language-specific
    post-processing to generated code examples.
    
    Args:
        code: The generated code to fix
        language: The programming language of the code
        verbose: Whether to print verbose messages
        
    Returns:
        The fixed code
    """
    if language.lower() == "python":
        return _fix_python_code(code, verbose)
    # Future language-specific fixes can be added here:
    # elif language.lower() == "javascript":
    #     return _fix_javascript_code(code, verbose)
    # elif language.lower() == "java":
    #     return _fix_java_code(code, verbose)
    # elif language.lower() == "cpp" or language.lower() == "c++":
    #     return _fix_cpp_code(code, verbose)
    
    return code


def _fix_python_code(code: str, verbose: bool = False) -> str:
    """
    Apply Python-specific fixes to generated code.
    
    Args:
        code: The Python code to fix
        verbose: Whether to print verbose messages
        
    Returns:
        The fixed Python code
    """
    try:
        from .fix_external_imports import fix_external_imports_in_content
        # Note: We don't have access to the original code_module here,
        # so we'll just fix the double def issue and external imports
        fixed_code, was_fixed = fix_external_imports_in_content(code, "")
        if was_fixed and verbose:
            print("[yellow]Fixed external imports in generated Python example[/yellow]")
        return fixed_code
    except ImportError as e:
        if verbose:
            print(f"[yellow]Warning: Could not import fix_external_imports: {e}[/yellow]")
    except Exception as e:
        if verbose:
            print(f"[yellow]Warning: Error applying Python fixes: {e}[/yellow]")
    
    return code


class ExtractedCode(BaseModel):
    """Pydantic model for the extracted code."""
    extracted_code: str = Field(description="The extracted code from the LLM output")

def postprocess_0(text: str) -> str:
    """
    Simple code extraction for strength = 0.
    Extracts code between triple backticks.
    """
    lines = text.split('\n')
    code_lines = []
    in_code_block = False
    
    for line in lines:
        if '```' in line: # MODIFIED: Was line.startswith('```')
            if not in_code_block:
                # Skip the language identifier line / content on opening delimiter line
                in_code_block = True
                continue
            else:
                # Content on closing delimiter line is skipped
                in_code_block = False
                continue
        if in_code_block:
            code_lines.append(line)
    
    return '\n'.join(code_lines)

def postprocess(
    llm_output: str,
    language: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0,
    time: float = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[str, float, str]:
    """
    Extract code from LLM output string.
    
    Args:
        llm_output (str): The string output from the LLM containing code sections
        language (str): The programming language of the code to extract
        strength (float): The strength of the LLM model to use (0-1)
        temperature (float): The temperature parameter for the LLM (0-1)
        time (float): The thinking effort for the LLM model (0-1)
        verbose (bool): Whether to print detailed processing information
    
    Returns:
        Tuple[str, float, str]: (extracted_code, total_cost, model_name)
    """
    try:
        # Input validation
        if not llm_output or not isinstance(llm_output, str):
            raise ValueError("llm_output must be a non-empty string")
        if not language or not isinstance(language, str):
            raise ValueError("language must be a non-empty string")
        if not 0 <= strength <= 1:
            raise ValueError("strength must be between 0 and 1")
        if not 0 <= temperature <= 1:
            raise ValueError("temperature must be between 0 and 1")

        # Step 1: If strength is 0, use simple extraction
        if strength == 0:
            if verbose:
                print("[blue]Using simple code extraction (strength = 0)[/blue]")
            return (postprocess_0(llm_output), 0.0, "simple_extraction")

        # Step 2: Load the prompt template
        prompt_template = load_prompt_template("extract_code_LLM")
        if not prompt_template:
            raise ValueError("Failed to load prompt template")

        if verbose:
            print("[blue]Loaded prompt template for code extraction[/blue]")

        # Step 3: Process using llm_invoke
        input_json = {
            "llm_output": llm_output,
            "language": language
        }

        response = llm_invoke(
            prompt=prompt_template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            output_pydantic=ExtractedCode
        )

        if not response or 'result' not in response:
            raise ValueError("Failed to get valid response from LLM")

        extracted_code_obj: ExtractedCode = response['result'] # Renamed for clarity
        code_text = extracted_code_obj.extracted_code

        # Step 3c: Remove triple backticks and language identifier if present
        lines = code_text.split('\n')
        if lines and lines[0].startswith('```'):
            lines = lines[1:]
        if lines and lines[-1].startswith('```'): # Check if lines is not empty again after potentially removing first line
            lines = lines[:-1]
        
        final_code = '\n'.join(lines)

        # Step 3d: Apply language-specific fixes
        final_code = _apply_language_specific_fixes(final_code, language, verbose)

        if verbose:
            print("[green]Successfully extracted code[/green]")

        # Step 4: Return the results
        return (
            final_code,
            response['cost'],
            response['model_name']
        )

    except Exception as e:
        print(f"[red]Error in postprocess: {str(e)}[/red]")
        raise
