import sys
import os
import tempfile
import textwrap

# =============================================================================
# Path Setup
# =============================================================================
# Add the parent directory to sys.path to allow importing from src.
# This assumes the script is run from the 'examples' directory relative to the project root.
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..'))
sys.path.append(project_root)

# Import the module to be demonstrated
try:
    from src.utils import helpers
except ImportError:
    print("Error: Could not import 'src.utils.helpers'. Ensure your project structure is correct.")
    sys.exit(1)

def main():
    print("=== PDD Prompt Linter: Helpers Module Demo ===\n")

    # =========================================================================
    # 1. File I/O and Normalization
    # =========================================================================
    print("--- 1. File I/O & Normalization ---")
    
    # Create a temporary file with messy line endings and whitespace
    messy_content = (
        "Hello World!   \r\n"
        "This file has mixed line endings.\n"
        "   And trailing spaces.   \r"
    )
    
    with tempfile.NamedTemporaryFile(mode='w', delete=False, encoding='utf-8') as tmp:
        tmp.write(messy_content)
        tmp_path = tmp.name

    try:
        print(f"Reading file: {tmp_path}")
        # read_file_content automatically normalizes line endings and strips trailing whitespace
        clean_content = helpers.read_file_content(tmp_path)
        
        print("\n[Raw Content (repr)]:")
        print(repr(messy_content))
        
        print("\n[Cleaned Content (repr)]:")
        print(repr(clean_content))
        
        # Verify normalization
        assert "\r" not in clean_content
        
        # The line in question is: "   And trailing spaces."
        # We verify it does not end with space, and matches expected content.
        # (Previous assertion failed because it flagged the leading spaces as well)
        target_line = clean_content.split('\n')[2]
        assert not target_line.endswith("   ") # Trailing space check
        assert target_line == "   And trailing spaces." # Content check
        
        print("\nSuccess: Text normalized correctly.")

    finally:
        # Cleanup
        if os.path.exists(tmp_path):
            os.remove(tmp_path)

    # =========================================================================
    # 2. Tag Detection & Extraction
    # =========================================================================
    print("\n--- 2. Tag Detection ---")

    sample_prompt = """
    Here is a prompt with some PDD tags.
    
    <include>src/core/logic.py</include>
    
    Some instructions here.
    
    <web>
        https://example.com/api-docs
    </web>
    
    <include>src/utils/helpers.py</include>
    """

    # Count specific tags
    include_count = helpers.count_tags(sample_prompt, helpers.TAG_INCLUDE)
    web_count = helpers.count_tags(sample_prompt, helpers.TAG_WEB)
    
    print(f"Found {include_count} <{helpers.TAG_INCLUDE}> tags.")
    print(f"Found {web_count} <{helpers.TAG_WEB}> tags.")

    # Extract content
    includes = helpers.extract_tag_content(sample_prompt, helpers.TAG_INCLUDE)
    print(f"\nExtracted Includes: {includes}")
    
    # Note: extract_tag_content strips whitespace from the result
    web_links = helpers.extract_tag_content(sample_prompt, helpers.TAG_WEB)
    print(f"Extracted Web Links: {web_links}")

    # =========================================================================
    # 3. Heuristic Content Analysis (Code vs. Text Ratio)
    # =========================================================================
    print("\n--- 3. Code vs. Text Ratio Analysis ---")

    # Use textwrap.dedent to ensure the indentation of the Python file 
    # doesn't artificially inflate the "code" score (based on indentation heuristic).

    # Case A: Mostly Natural Language
    text_heavy = textwrap.dedent("""
    You are a helpful assistant.
    Please write a poem about the ocean.
    The poem should be rhyming and include references to fish.
    """)
    
    # Case B: Mostly Code
    code_heavy = textwrap.dedent("""
    def calculate_sum(a, b):
        return a + b

    class Processor:
        def __init__(self):
            self.data = []
            
        def process(self):
            if self.data:
                return True
    """)

    ratio_text = helpers.calculate_code_ratio(text_heavy)
    ratio_code = helpers.calculate_code_ratio(code_heavy)

    print(f"Text-heavy score (0.0 = text, 1.0 = code): {ratio_text}")
    print(f"Code-heavy score (0.0 = text, 1.0 = code): {ratio_code}")

    if ratio_code > 0.5:
        print("-> 'code_heavy' correctly identified as primarily code.")
    
    if ratio_text < 0.2:
        print("-> 'text_heavy' correctly identified as primarily natural language.")

if __name__ == "__main__":
    main()