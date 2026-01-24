import sys
import os
import logging
from pathlib import Path

# --- Path Setup ---
# Add the project root to sys.path to allow imports from 'src'
# This assumes the script is running from <project_root>/examples/
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# --- Imports ---
try:
    from src.utils.pipeline import lint_text, lint_file, LintConfig
    from src.utils.models import Severity
except ImportError as e:
    print(f"Import Error: {e}")
    print("Ensure you are running this script within the correct project structure.")
    sys.exit(1)

# Configure logging to see pipeline warnings/info
logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')

def print_report_summary(report, title: str):
    """Helper function to print a readable summary of the Report object."""
    print(f"\n{'='*10} {title} {'='*10}")
    print(f"Source:   {report.filepath}")
    print(f"Score:    {report.score}/100")
    print(f"Summary:  {report.summary}")
    
    print(f"Issues:   {len(report.issues)}")
    for issue in report.issues:
        # Simple visual indicator for severity
        icon = "🔴" if issue.severity == Severity.ERROR else "🟠" if issue.severity == Severity.WARNING else "🔵"
        print(f"  {icon} [{issue.rule_id}] {issue.title}")

    # Check if a fix was generated (dynamically attached attribute)
    if hasattr(report, "suggested_fix") and report.suggested_fix:
        print(f"\n[+] Suggested Fix Generated ({len(report.suggested_fix)} chars)")
    print("="*40)

def main():
    """
    Demonstrates three common usage patterns for the pipeline module.
    """

    # --- Scenario 1: Fast Linting (Heuristics Only) ---
    # Useful for real-time checks where latency matters (e.g., IDE plugins).
    print("\n--- Scenario 1: Fast Linting (No LLM) ---")
    
    raw_text = "Write a python script to scrape google."
    
    # Disable LLM and Fix generation for speed
    fast_config = LintConfig(
        use_llm=False,
        generate_fix=False
    )
    
    report = lint_text(raw_text, config=fast_config)
    print_report_summary(report, "Heuristic Report")


    # --- Scenario 2: Full Analysis with Fix Generation ---
    # Useful for CI/CD pipelines or "Fix My Prompt" buttons.
    print("\n--- Scenario 2: Full Analysis (LLM + Fixes) ---")
    
    # Note: If API keys are missing, the pipeline will gracefully degrade to heuristics
    full_config = LintConfig(
        use_llm=True,
        generate_fix=True,
        llm_timeout=15,  # Set a custom timeout
        # Custom weights can be provided to prioritize specific categories
        weights={
            "modularity": 40, # Increase importance of modularity
            "contracts": 20,
            "context": 20,
            "determinism": 10,
            "abstraction": 10
        }
    )

    prompt_text = """
    <prompt>
    System: You are a helpful assistant.
    Please write code.
    </prompt>
    """
    
    report_full = lint_text(prompt_text, config=full_config)
    print_report_summary(report_full, "Full Report")


    # --- Scenario 3: File-based Linting ---
    # Useful for CLI tools processing files from disk.
    print("\n--- Scenario 3: File Linting ---")
    
    # Create a dummy file for demonstration
    dummy_path = Path("demo_prompt.txt")
    dummy_path.write_text("This prompt is missing tags and context.", encoding="utf-8")
    
    try:
        # lint_file handles file reading and existence checks automatically
        report_file = lint_file(dummy_path, config=LintConfig(use_llm=False))
        print_report_summary(report_file, "File Report")
    finally:
        # Cleanup
        if dummy_path.exists():
            dummy_path.unlink()

if __name__ == "__main__":
    main()