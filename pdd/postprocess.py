from typing import Tuple
from rich import print
from pydantic import BaseModel, Field
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import DEFAULT_TIME, DEFAULT_STRENGTH

def _apply_language_specific_fixes(code: str, language: str, verbose: bool = False) -> str:
    """
    Apply language-independent fixes to generated code.
    
    Since we now use prompt-based solutions to prevent issues like external imports
    and syntax errors, this function focuses on minimal, universal fixes that
    can apply to any programming language.
    
    Args:
        code: The generated code to fix
        language: The programming language of the code (for logging purposes)
        verbose: Whether to print verbose messages
        
    Returns:
        The fixed code
    """
    # Apply minimal, universal fixes
    code = _apply_universal_fixes(code, verbose)
    
    if verbose:
        print(f"[green]Applied language-independent fixes for {language}[/green]")
    
    return code


def _apply_universal_fixes(code: str, verbose: bool = False) -> str:
    """
    Apply universal fixes that work across all programming languages.
    
    These are minimal fixes for common issues that can occur in any language,
    such as double keywords or basic syntax errors.
    
    Args:
        code: The generated code to fix
        verbose: Whether to print verbose messages
        
    Returns:
        The fixed code
    """
    import re
    
    # Fix double keywords that can occur in any language
    # This pattern catches common double declarations across languages
    double_keyword_pattern = r'\b(def|function|class|public|private|protected|static|const|let|var)\s+\1\b'
    
    original_code = code
    code = re.sub(double_keyword_pattern, r'\1', code)
    
    if verbose and code != original_code:
        print("[yellow]Fixed double keyword declarations in generated code[/yellow]")
    
    # Fix common whitespace issues that can occur in any language
    # Remove excessive blank lines (more than 2 consecutive)
    code = re.sub(r'\n\s*\n\s*\n+', '\n\n', code)
    
    # Fix trailing whitespace on lines
    code = re.sub(r'[ \t]+$', '', code, flags=re.MULTILINE)
    
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
