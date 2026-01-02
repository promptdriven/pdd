import sys
import os
import json

# Add the parent directory to sys.path to allow importing the module
# This assumes the script is run from the 'examples' directory and the module is in 'src/backend/models'
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, ".."))
sys.path.insert(0, project_root)

try:
    from src.backend.models.findings import (
        LintReport,
        Summary,
        IssueCounts,
        Finding,
        Severity,
        Evidence,
        SuggestedEdit,
    )
except ImportError:
    print("Error: Could not import 'src.backend.models.findings'.")
    print("Ensure your project structure matches the expected layout.")
    sys.exit(1)


def create_example_report():
    """
    Demonstrates how to instantiate the Pydantic models to create a full LintReport.
    """
    print("--- Creating a Lint Report ---")

    # 1. Create Evidence (optional, used if the finding is tied to specific lines)
    evidence_loc = Evidence(line_start=10, line_end=12)

    # 2. Create Suggested Edits (optional)
    fix_proposal = SuggestedEdit(
        kind="replace",
        snippet="You are a helpful AI assistant."
    )

    # 3. Create Findings
    # Finding 1: An error with evidence and a fix
    finding_1 = Finding(
        rule_id="PDD001",
        severity=Severity.ERROR,
        title="Ambiguous Persona",
        message="The prompt lacks a clear persona definition.",
        evidence=evidence_loc,
        suggested_edits=[fix_proposal]
    )

    # Finding 2: A warning without specific line numbers (file-level issue)
    finding_2 = Finding(
        rule_id="PDD005",
        severity=Severity.WARN,
        title="High Token Count",
        message="The prompt is approaching the context window limit.",
        evidence=None  # Explicitly None for file-level
    )

    # 4. Create Summary Statistics
    # In a real app, you would calculate these based on the list of findings
    stats = IssueCounts(error=1, warn=1, info=0)
    
    summary_data = Summary(
        score=85,
        issue_counts=stats,
        token_count_estimate=1024
    )

    # 5. Create the Root Report
    report = LintReport(
        filename="prompts/chatbot_v1.txt",
        summary=summary_data,
        findings=[finding_1, finding_2]
    )

    return report


def demonstrate_serialization(report: LintReport):
    """
    Demonstrates how to serialize the report to JSON, which is useful for API responses or CLI output.
    """
    print("\n--- Serializing to JSON ---")
    
    # model_dump_json() is the standard Pydantic v2 method for JSON serialization
    json_output = report.model_dump_json(indent=2)
    print(json_output)


def demonstrate_validation_error():
    """
    Demonstrates that Pydantic enforces types and constraints.
    """
    print("\n--- Demonstrating Validation Logic ---")
    try:
        # Attempting to create a Summary with an invalid score (must be 0-100)
        Summary(
            score=150,  # Invalid: > 100
            issue_counts=IssueCounts(),
            token_count_estimate=100
        )
    except Exception as e:
        print(f"Caught expected validation error: {e}")


if __name__ == "__main__":
    # 1. Build the object graph
    my_report = create_example_report()
    
    # 2. Access data safely (typed fields)
    print(f"\nReport for file: {my_report.filename}")
    print(f"Total Errors: {my_report.summary.issue_counts.error}")
    print(f"First Finding Rule ID: {my_report.findings[0].rule_id}")

    # 3. Show JSON output
    demonstrate_serialization(my_report)

    # 4. Show error handling
    demonstrate_validation_error()