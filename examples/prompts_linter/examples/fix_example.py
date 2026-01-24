import sys
import os
import logging

# --- Path Setup for Example ---
# Add the parent directory to sys.path to simulate running from within the project structure.
# This allows us to import 'src.utils.fix' and 'src.utils.models'.
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.abspath(os.path.join(current_dir, '..'))
if parent_dir not in sys.path:
    sys.path.insert(0, parent_dir)

# --- Imports ---
from src.utils.models import (
    Report, 
    Issue, 
    Severity, 
    RuleCategory, 
    LLMResponse, 
    LLMSuggestionDetail
)
from src.utils.fix import apply_fixes

# Configure logging to see the output from the fix module
logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')

def get_safe_rule_category():
    """
    Safely retrieves a valid RuleCategory member.
    Handles cases where 'STRUCTURE' might be missing or named differently.
    """
    # 1. Try the expected name
    if hasattr(RuleCategory, 'STRUCTURE'):
        return RuleCategory.STRUCTURE
    
    # 2. Try common alternatives
    for name in ['STRUCTURAL', 'SYNTAX', 'FORMAT', 'CONTENT']:
        if hasattr(RuleCategory, name):
            return getattr(RuleCategory, name)
            
    # 3. Fallback: Try to grab the first available member if it's an iterable Enum
    try:
        return list(RuleCategory)[0]
    except (TypeError, IndexError):
        pass
        
    # 4. Last resort: Return None (Issue model might accept None)
    return None

def main():
    print("=== PDD Prompt Fixer Example ===\n")

    # 1. Define a broken prompt text
    # This text is missing the root <prompt> tags and has a generic placeholder
    # that the LLM suggests replacing.
    original_text = """
This is a system prompt for a coding assistant.
Please write code in Python.
"""
    print(f"--- Original Text ---\n{original_text}\n---------------------")

    # 2. Create a Mock Report
    # We simulate a report that identifies structural issues (missing tags)
    # and includes LLM suggestions for content improvement.
    
    # Determine a valid category to avoid AttributeError
    safe_category = get_safe_rule_category()
    
    # Issue: Missing root tags (triggers structural scaffolding)
    structural_issue = Issue(
        rule_id="STR001",
        line_number=1,
        severity=Severity.ERROR,
        category=safe_category,
        description="Missing <prompt> root tags.",
        fix_suggestion="Wrap content in <prompt> tags."
    )

    # LLM Suggestion: Improve specificity (triggers content patching)
    # Using LLMSuggestionDetail as required by LLMResponse model
    llm_suggestion = LLMSuggestionDetail(
        rule_id="CTX005",
        title="Specify Persona",
        rationale="Defining a persona improves output quality.",
        before="This is a system prompt for a coding assistant.",
        after="You are an expert Python software engineer.",
        priority="High"
    )

    llm_response = LLMResponse(
        guide_alignment_summary="Needs structural and context fixes.",
        top_fixes=[],
        suggestions=[llm_suggestion]
    )

    report = Report(
        filepath="example_prompt.txt",
        score=50,
        issues=[structural_issue],
        summary="Critical structural failure.",
        llm_analysis=llm_response
    )

    # 3. Apply Fixes
    # The apply_fixes function will:
    #   a. Detect STR001 and wrap the text in <prompt> tags.
    #   b. Detect the LLM suggestion and replace the generic sentence with the persona.
    print("\nApplying fixes...")
    fixed_text = apply_fixes(original_text, report)

    # 4. Display Result
    print(f"\n--- Fixed Text ---\n{fixed_text}\n------------------")

    # Verification
    if "<prompt>" in fixed_text and "You are an expert Python software engineer" in fixed_text:
        print("\nSUCCESS: Structural tags added and content patched.")
    else:
        print("\nFAILURE: Fixes were not applied correctly.")

if __name__ == "__main__":
    main()