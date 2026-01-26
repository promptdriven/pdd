import sys
import os
from typing import List

# --- Path Setup for Example ---
# Add the parent directory to sys.path to simulate running from within the project structure
# This allows us to import 'src.utils.report' and 'src.utils.models'
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# --- Imports ---
try:
    from src.utils.models import Report, Issue, Severity, RuleCategory, LLMResponse
    from src.utils.report import render_report
except ImportError as e:
    print(f"Error importing modules: {e}")
    print("Please ensure you are running this script from the 'examples' directory and that 'src' exists in the parent directory.")
    sys.exit(1)

def create_mock_report() -> Report:
    """
    Helper function to create a dummy Report object with issues and LLM analysis.
    """
    # 1. Create some mock issues
    issue1 = Issue(
        rule_id="MOD001",
        line_number=15,
        severity=Severity.ERROR,
        category=RuleCategory.MODULARITY,
        description="Prompt exceeds 500 tokens without sub-prompt division.",
        fix_suggestion="Split into 'context' and 'instruction' sections."
    )

    # Note: Using RuleCategory.MODULARITY for all issues to ensure compatibility 
    # with the current definition of RuleCategory in src.utils.models.
    issue2 = Issue(
        rule_id="SEC002",
        line_number=42,
        severity=Severity.WARNING,
        category=RuleCategory.MODULARITY, # Changed from SECURITY to avoid AttributeError
        description="Potential PII placeholder detected: {{user_email}}.",
        fix_suggestion="Ensure PII is scrubbed before injection."
    )

    issue3 = Issue(
        rule_id="STY005",
        line_number=1,
        severity=Severity.INFO,
        category=RuleCategory.MODULARITY, # Changed from STYLE to avoid potential AttributeError
        description="Consider adding a version tag to the header.",
        fix_suggestion="Add 'Version: 1.0' to the top."
    )

    # 2. Create mock LLM analysis
    llm_analysis = LLMResponse(
        guide_alignment_summary="The prompt is generally well-structured but lacks specific persona definitions.",
        top_fixes=[],
        suggestions=[]
    )

    # 3. Assemble the Report
    return Report(
        filepath="prompts/customer_service_agent.txt",
        score=75,
        issues=[issue1, issue2, issue3],
        summary="Moderate quality prompt. Critical modularity issue detected.",
        llm_analysis=llm_analysis
    )

def main():
    print("Generating Mock Report...")
    report = create_mock_report()

    # --- Example 1: Render to Console (Rich Text) ---
    print("\n" + "="*50)
    print("EXAMPLE 1: Rendering to Console (Text)")
    print("="*50 + "\n")
    
    # This will print the colorful table and panels directly to stdout
    render_report(report, fmt="text")


    # --- Example 2: Render to JSON String ---
    print("\n" + "="*50)
    print("EXAMPLE 2: Rendering to JSON (Stdout)")
    print("="*50 + "\n")
    
    # This prints the raw JSON string
    render_report(report, fmt="json")


    # --- Example 3: Render to Markdown File ---
    print("\n" + "="*50)
    print("EXAMPLE 3: Rendering to Markdown File")
    print("="*50 + "\n")
    
    output_md_path = os.path.join(current_dir, "report_output.md")
    render_report(report, fmt="md", output_path=output_md_path)
    
    print(f"Markdown report written to: {output_md_path}")
    print("Preview of file content:")
    with open(output_md_path, "r") as f:
        print(f.read())


    # --- Example 4: Render Text to File (Plain Text) ---
    print("\n" + "="*50)
    print("EXAMPLE 4: Rendering Text to File (Stripped ANSI)")
    print("="*50 + "\n")
    
    output_txt_path = os.path.join(current_dir, "report_output.txt")
    # When output_path is provided for 'text' format, the module strips colors
    # so the file is readable in standard editors.
    render_report(report, fmt="text", output_path=output_txt_path)
    
    print(f"Plain text report written to: {output_txt_path}")

    # Cleanup generated files
    # os.remove(output_md_path)
    # os.remove(output_txt_path)

if __name__ == "__main__":
    main()