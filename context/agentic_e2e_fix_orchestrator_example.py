"""
Example usage of the agentic_e2e_fix_orchestrator module.

This script demonstrates how to invoke the `run_agentic_e2e_fix_orchestrator` function.
Since the orchestrator relies on internal modules like `run_agentic_task` and `load_prompt_template`,
this example mocks those dependencies to simulate a successful e2e fix workflow
without making actual LLM calls or requiring a real GitHub issue.

Scenario:
    We simulate an issue where e2e tests are failing due to a bug in the payment processing module.
    The orchestrator will step through the 9-step process across multiple cycles,
    running unit tests, identifying root causes, and applying fixes via pdd fix.
"""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
# Adjust this path based on your actual project structure relative to this script
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    # Import the module to be tested
    # Note: We assume the file is at pdd/agentic_e2e_fix_orchestrator.py
    from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
except ImportError:
    print("Error: Could not import 'pdd.agentic_e2e_fix_orchestrator'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_load_prompt_template(template_name: str) -> str:
    """
    Mock implementation of load_prompt_template.
    Returns a dummy prompt string based on the requested template name.
    """
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, timeout: float = None):
    """
    Mock implementation of run_agentic_task.
    Simulates the output of an LLM agent for each step of the e2e fix workflow.

    Returns:
        Tuple[bool, str, float, str]: (success, output, cost, provider)
        Note: The real run_agentic_task returns a 4-tuple. File tracking is done
        by parsing FILES_CREATED/FILES_MODIFIED lines from the output string.
    """
    # Extract step number from label (e.g., "step1", "step2", etc.)
    step_num = label.replace("step", "")

    # Default return values
    success = True
    cost = 0.20  # Simulated cost per step
    provider = "anthropic-mock"
    output = ""

    if step_num == "1":
        output = "Ran unit tests from issue. 2 tests failed: test_payment_validation, test_refund_calculation. Running pdd fix on payment_processor dev unit."
    elif step_num == "2":
        # First cycle: tests fail. Second cycle: tests pass (simulated by checking label for cycle info)
        if "cycle2" in instruction.lower():
            output = "ALL_TESTS_PASS\nAll e2e tests passed successfully."
        else:
            output = "E2E tests failed:\n- test_checkout_flow: AssertionError in payment step\n- test_subscription_renewal: Unexpected error in billing"
    elif step_num == "3":
        output = "Root cause analysis:\n- test_checkout_flow: CODE_BUG - payment_processor.py missing currency validation\n- test_subscription_renewal: TEST_BUG - incorrect expected value in assertion"
    elif step_num == "4":
        output = "Fixed e2e test: test_subscription_renewal - corrected expected billing amount from $9.99 to $10.99.\nFILES_MODIFIED: tests/e2e/test_subscription.py"
    elif step_num == "5":
        output = "Dev units involved in failures:\n- payment_processor (primary)\n- currency_converter (secondary)\nDEV_UNITS_IDENTIFIED: payment_processor, currency_converter"
    elif step_num == "6":
        output = "Created unit tests for identified dev units:\n- tests/test_payment_processor_bug.py: test_validate_currency_code\n- tests/test_currency_converter_bug.py: test_convert_zero_amount\nFILES_CREATED: tests/test_payment_processor_bug.py, tests/test_currency_converter_bug.py"
    elif step_num == "7":
        output = "Verification complete:\n- test_validate_currency_code: FAILS as expected (bug detected)\n- test_convert_zero_amount: FAILS as expected (bug detected)\nUnit tests successfully detect the bugs."
    elif step_num == "8":
        output = "Running pdd fix on failing dev units:\n- payment_processor: FIXED (1 attempt)\n- currency_converter: FIXED (2 attempts)\nFILES_MODIFIED: pdd/payment_processor.py, pdd/currency_converter.py"
    elif step_num == "9":
        # Second cycle: all tests pass
        if "cycle2" in instruction.lower():
            output = "Final verification:\n- Unit tests: 4/4 passing\n- E2e tests: 2/2 passing\n\n**Status:** ALL_TESTS_PASS\n\nAll bugs fixed successfully."
        else:
            output = "Final verification:\n- Unit tests: 4/4 passing\n- E2e tests: 1/2 passing (1 still failing)\n\n**Status:** CONTINUE_CYCLE\n\nProceeding to next cycle."
    else:
        output = "Unknown step executed."

    # Return 4-tuple matching real run_agentic_task signature
    return success, output, cost, provider


def main():
    """Main function to run the agentic e2e fix orchestrator simulation."""
    # Define dummy issue data
    issue_data = {
        "issue_url": "https://github.com/example/payments/issues/123",
        "issue_content": """Issue: Payment processing fails for certain currencies

E2E tests identified:
- tests/e2e/test_checkout.py::test_checkout_flow
- tests/e2e/test_subscription.py::test_subscription_renewal

Unit tests created by pdd bug:
- tests/test_payment_bug.py::test_payment_validation
- tests/test_payment_bug.py::test_refund_calculation

Error trace shows currency validation is missing for non-USD currencies.""",
        "repo_owner": "example",
        "repo_name": "payments",
        "issue_number": 123,
        "issue_author": "qa_engineer",
        "issue_title": "Payment processing fails for EUR currency",
        "cwd": Path("./temp_workspace"),
        "timeout_adder": 30.0,
        "max_cycles": 5,
        "resume": False,
        "verbose": True,
        "quiet": False
    }

    print("Starting Agentic E2E Fix Orchestrator Simulation...")
    print("-" * 60)

    # Patch the internal dependencies
    # We patch where they are imported IN the orchestrator module, not where they are defined
    with patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
         patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task):

        # Run the orchestrator
        success, final_msg, total_cost, model, changed_files = run_agentic_e2e_fix_orchestrator(
            **issue_data
        )

    print("-" * 60)
    print("Simulation Complete.")
    print(f"Success: {success}")
    print(f"Final Message: {final_msg}")
    print(f"Total Cost: ${total_cost:.2f}")
    print(f"Model Used: {model}")
    print(f"Changed Files: {changed_files}")


if __name__ == "__main__":
    main()
