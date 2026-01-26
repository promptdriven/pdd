import sys
import os
import textwrap

# =============================================================================
# Path Setup
# =============================================================================
# Add the parent directory to sys.path to allow importing from src.
# This assumes the script is run from the 'examples' directory relative to the project root.
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..'))
sys.path.append(project_root)

try:
    from src.utils import rules
    from src.utils.models import Severity
except ImportError as e:
    print(f"Error: Could not import project modules. Ensure your project structure is correct.\nDetails: {e}")
    sys.exit(1)

def print_issues(title: str, issues: list):
    """Helper to pretty-print a list of issues."""
    print(f"\n{'='*60}")
    print(f"ANALYSIS: {title}")
    print(f"{'='*60}")
    
    if not issues:
        print("✅ No issues found! The prompt looks compliant.")
        return

    print(f"Found {len(issues)} issue(s):\n")
    for i, issue in enumerate(issues, 1):
        # Determine icon based on severity
        icon = "🔴" if issue.severity == Severity.ERROR else \
               "🟠" if issue.severity == Severity.WARNING else "🔵"
        
        print(f"{i}. {icon} [{issue.rule_id}] {issue.title}")
        print(f"   Category: {issue.category.value}")
        print(f"   Details:  {issue.description}")
        print("-" * 40)

def main():
    """
    Demonstrates the usage of rules.analyze_text() on various prompt examples.
    """
    
    # -------------------------------------------------------------------------
    # Example 1: A Compliant PDD Prompt
    # -------------------------------------------------------------------------
    # This prompt follows the PDD structure: Requirements, I/O, Dependencies, Instructions.
    compliant_prompt = textwrap.dedent("""
    # Requirements
    1. Create a function that adds two numbers.
    2. Handle type errors gracefully.

    # Input/Output
    - Input: Two integers
    - Output: Integer sum

    # Dependencies
    - None

    # Instructions
    Please implement the `add` function in Python.
    Ensure you add type hints.
    """)

    issues_1 = rules.analyze_text(compliant_prompt)
    print_issues("Compliant Prompt", issues_1)


    # -------------------------------------------------------------------------
    # Example 2: A Non-Deterministic Prompt
    # -------------------------------------------------------------------------
    # This prompt uses forbidden tags like <web> and <run>.
    non_deterministic_prompt = textwrap.dedent("""
    # Requirements
    1. Fetch the latest stock prices.

    # Instructions
    <web>https://finance.yahoo.com</web>
    
    Please <run>python script.py</run> to verify the data.
    """)

    issues_2 = rules.analyze_text(non_deterministic_prompt)
    print_issues("Non-Deterministic Prompt", issues_2)


    # -------------------------------------------------------------------------
    # Example 3: A "Repo Dump" Prompt
    # -------------------------------------------------------------------------
    # This prompt dumps a massive amount of code directly into the context
    # instead of using <include> tags, and lacks structure.
    
    # Generating fake code lines to trigger the ratio check
    fake_code = "\n".join([f"    def function_{i}(): pass" for i in range(60)])
    
    repo_dump_prompt = f"""
    Here is the entire codebase for you to fix.
    
    {fake_code}
    
    Fix the bugs in the full codebase.
    """

    issues_3 = rules.analyze_text(repo_dump_prompt)
    print_issues("Repo Dump Prompt", issues_3)


    # -------------------------------------------------------------------------
    # Example 4: Broken Anatomy & Modularity Violations
    # -------------------------------------------------------------------------
    # This prompt tries to define multiple files and misses required sections.
    broken_prompt = textwrap.dedent("""
    # file: src/main.py
    print("Hello")
    
    ---
    
    # file: src/utils.py
    def help(): pass
    
    Just write these files for me.
    """)

    issues_4 = rules.analyze_text(broken_prompt)
    print_issues("Broken Anatomy & Modularity", issues_4)

if __name__ == "__main__":
    main()