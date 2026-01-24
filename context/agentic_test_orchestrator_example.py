"""
Example usage of the agentic_test_orchestrator module.

This script demonstrates how to invoke the `run_agentic_test_orchestrator` function.
Since the orchestrator relies on internal modules like `run_agentic_task` and `load_prompt_template`,
this example mocks those dependencies to simulate a successful UI test generation workflow
without making actual LLM calls or requiring a real GitHub issue.

Scenario:
    We simulate an issue where a user requests UI tests for a login page.
    The orchestrator will step through the 9-step process:
    1. Check for duplicate test requests
    2. Review codebase documentation
    3. Analyze and ask clarifying questions if needed
    4. Detect frontend type (web/CLI/desktop)
    5. Create test plan
    6. Generate UI tests
    7. Run tests
    8. Fix and iterate on failing tests
    9. Submit PR
"""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the project root is in sys.path so we can import the module
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator
except ImportError:
    print("Error: Could not import 'pdd.agentic_test_orchestrator'.")
    print("Ensure your PYTHONPATH is set correctly or the file structure matches.")
    sys.exit(1)


def mock_load_prompt_template(template_name: str) -> str:
    """
    Mock implementation of load_prompt_template.
    Returns a dummy prompt string based on the requested template name.
    """
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, timeout: float = None, max_retries: int = 3):
    """
    Mock implementation of run_agentic_task.
    Simulates the output of an LLM agent for each step of the 9-step UI test workflow.
    """
    step_num = label.replace("step", "")

    # Default return values
    success = True
    cost = 0.15  # Simulated cost per step
    provider = "anthropic"
    output = ""

    if step_num == "1":
        output = "No duplicate test requests found. Proceeding with UI test generation."
    elif step_num == "2":
        output = """Codebase review complete:
        - Frontend: Next.js application in /frontend
        - Auth pages: /frontend/pages/auth/login.tsx, /frontend/pages/auth/register.tsx
        - Components: LoginForm, RegisterForm in /frontend/components/auth/
        - API routes: /api/auth/login, /api/auth/register"""
    elif step_num == "3":
        output = """Requirements are clear:
        - Test login page functionality
        - Verify form validation (email format, password requirements)
        - Test successful and failed login scenarios
        - No clarification needed from author."""
    elif step_num == "4":
        output = """Frontend detected: Next.js (React)
        Test framework: Playwright
        Base URL: http://localhost:3000
        Authentication: Session-based via NextAuth.js"""
    elif step_num == "5":
        output = """Test Plan:
        1. Login page renders correctly
        2. Form validation - invalid email shows error
        3. Form validation - password too short shows error
        4. Successful login redirects to dashboard
        5. Failed login shows error message
        6. Remember me checkbox persists session

        Estimated tests: 6 test cases
        Files to create: tests/e2e/login.spec.ts"""
    elif step_num == "6":
        output = """FILES_CREATED: tests/e2e/login.spec.ts

        Generated Playwright test file with 6 test cases:
        - test('login page renders correctly')
        - test('shows error for invalid email')
        - test('shows error for short password')
        - test('successful login redirects to dashboard')
        - test('failed login shows error message')
        - test('remember me persists session')"""
    elif step_num == "7":
        output = """Test execution results:
        6 tests total
        5 passed
        1 failed: 'remember me persists session' - localStorage not mocked

        Overall: 83% pass rate"""
    elif step_num == "8":
        output = """Fixed failing test:
        - Added localStorage mock in beforeEach hook
        - Re-ran tests: 6/6 passed

        FILES_MODIFIED: tests/e2e/login.spec.ts
        All tests now passing."""
    elif step_num == "9":
        output = """PR Created: https://github.com/example/myapp/pull/456

        Title: Add UI tests for login page (#123)
        Branch: test/issue-123
        Files: tests/e2e/login.spec.ts"""
    else:
        output = f"Unknown step executed: {step_num}"

    return success, output, cost, provider


def main():
    """Main function to run the agentic test orchestrator simulation."""
    # Define dummy issue data
    issue_data = {
        "issue_url": "https://github.com/example/myapp/issues/123",
        "issue_content": "Create UI tests for the login page. Should test form validation, successful login, and error handling.",
        "repo_owner": "example",
        "repo_name": "myapp",
        "issue_number": 123,
        "issue_author": "test_requester",
        "issue_title": "Add UI tests for login page",
        "cwd": Path("./temp_workspace"),
        "verbose": True,
        "quiet": False,
        "timeout_adder": 0.0,
        "use_github_state": False  # Disable for simulation
    }

    print("Starting Agentic UI Test Orchestrator Simulation...")
    print("-" * 60)

    # Patch the internal dependencies
    with patch("pdd.agentic_test_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
         patch("pdd.agentic_test_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task):

        # Run the orchestrator
        success, final_msg, total_cost, model, changed_files = run_agentic_test_orchestrator(
            **issue_data
        )

    print("-" * 60)
    print("Simulation Complete.")
    print(f"Success: {success}")
    print(f"Final Message: {final_msg}")
    print(f"Total Cost: ${total_cost:.2f}")
    print(f"Model Used: {model}")
    print(f"Changed Files: {changed_files}")
    print("\nNext step: Review the generated tests and merge the PR.")


if __name__ == "__main__":
    main()
