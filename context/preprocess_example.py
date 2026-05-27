import os
import sys
from pathlib import Path
from pdd.preprocess import preprocess

def main() -> None:
    """
    Example showing how to use the preprocess module to resolve tags 
    like <include>, <shell>, and handle template curly braces.
    """
    # Setup output directory for our example files
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)
    
    # Create a dummy Python file to include
    dummy_file = output_dir / "dummy.py"
    dummy_file.write_text("def hello():\n    return 'Hello from included file!'\n", encoding="utf-8")
    
    # Define a prompt with XML-like tags and template variables
    prompt_template = """\
Please review the following code:

<include>{dummy_file_path}</include>

Run result:
<shell>echo "Shell execution works!"</shell>

Note: {This should be doubled to prevent PromptTemplate errors}
"""
    # Format the prompt to inject the actual path
    raw_prompt = prompt_template.format(dummy_file_path=str(dummy_file))
    
    print("--- Raw Prompt ---")
    print(raw_prompt)
    
    # Process the prompt
    # recursive=False means we do a single pass and execute shell tags immediately.
    # double_curly_brackets=True means single braces will be doubled (e.g., for LangChain templates).
    processed_prompt = preprocess(
        prompt=raw_prompt,
        recursive=False,
        double_curly_brackets=True
    )
    
    print("--- Processed Prompt ---")
    print(processed_prompt)

if __name__ == "__main__":
    main()