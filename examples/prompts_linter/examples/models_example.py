import sys
import os
import json
from pydantic import ValidationError

# Add the parent directory to sys.path to import the module
# This assumes the script is run from the 'examples' directory
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from src.utils.models import (
    Severity,
    RuleCategory,
    Issue,
    Report,
    LLMResponse,
    LLMFixSuggestion,
    LLMSuggestionDetail
)

def main():
    print("--- 1. Creating an Issue ---")
    # Create a single linting issue
    issue = Issue(
        rule_id="MOD001",
        line_number=12,
        severity=Severity.WARNING,
        category=RuleCategory.MODULARITY,
        description="Prompt is too long and should be broken down.",
        fix_suggestion="Split the prompt into sub-prompts."
    )
    print(f"Created Issue: {issue.rule_id} ({issue.severity.value})")
    print(f"Description: {issue.description}")
    print("-" * 30)

    print("\n--- 2. Creating an LLM Response (Mock) ---")
    # Simulate a structured response from an LLM
    llm_data = {
        "guide_alignment_summary": "The prompt mostly follows PDD but lacks context.",
        "top_fixes": [
            {
                "title": "Add Context",
                "rationale": "The model needs to know who it is acting as.",
                "priority": "High"
            }
        ],
        "suggestions": [
            {
                "rule_id": "CTX001",
                "title": "Define Persona",
                "rationale": "Adding a persona improves response quality.",
                "before": "Write a poem.",
                "after": "You are a poet. Write a poem.",
                "priority": "High"
            }
        ],
        "extra_field_from_llm": "This should be ignored by the model config"
    }

    try:
        llm_response = LLMResponse(**llm_data)
        print("LLM Response parsed successfully.")
        print(f"Summary: {llm_response.guide_alignment_summary}")
        # Note: 'extra_field_from_llm' is stripped out automatically
        print(f"Extra fields ignored? {'extra_field_from_llm' not in llm_response.model_dump()}")
    except ValidationError as e:
        print(f"Validation failed: {e}")
    print("-" * 30)

    print("\n--- 3. Creating a Full Report ---")
    # Aggregate issues and LLM analysis into a full report
    report = Report(
        filepath="./prompts/main_prompt.txt",
        score=85,
        issues=[issue],
        summary="Good start, but needs modularity improvements.",
        llm_analysis=llm_response
    )

    print(f"Report for: {report.filepath}")
    print(f"Score: {report.score}")
    print(f"Is Clean (No Errors)? {report.is_clean}") # True because we only had a WARNING
    print("-" * 30)

    print("\n--- 4. Validation Logic (Score Bounds) ---")
    try:
        # Attempt to create an invalid report with score > 100
        Report(
            filepath="bad_file.txt",
            score=150, 
            issues=[],
            summary="Invalid score test"
        )
    except ValidationError as e:
        print("Caught expected validation error for score:")
        for err in e.errors():
            print(f" - {err['msg']}")
    print("-" * 30)

    print("\n--- 5. Serialization (JSON) ---")
    # Dump the full report to JSON
    json_output = report.model_dump_json(indent=2)
    print(json_output)

if __name__ == "__main__":
    main()