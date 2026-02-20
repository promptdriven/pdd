"""
Example usage of the agentic_checkup_orchestrator module.

This script demonstrates how to invoke `run_agentic_checkup_orchestrator`.
Since the orchestrator relies on internal modules like `run_agentic_task` and
`load_prompt_template`, this example mocks those dependencies to simulate
a successful 8-step checkup workflow without making actual LLM calls.

Scenario:
    We simulate a checkup for a CRM app where the orchestrator runs through
    all 10 steps (1, 2, 3, 4, 5, 6.1, 6.2, 6.3, 7, 8), discovers issues,
    fixes them, writes tests, verifies, and creates a PR.
"""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

try:
    from pdd.agentic_checkup_orchestrator import (
        run_agentic_checkup_orchestrator,
        STEP_ORDER,
        TOTAL_STEPS,
        MAX_FIX_VERIFY_ITERATIONS,
        _next_step,
        _parse_changed_files,
    )
except ImportError:
    print("Error: Could not import 'pdd.agentic_checkup_orchestrator'.")
    sys.exit(1)


def mock_load_prompt_template(template_name: str) -> str:
    """Mock implementation returning a dummy prompt."""
    return f"MOCK PROMPT FOR: {template_name}\nContext: {{issue_content}}"


def mock_run_agentic_task(instruction: str, cwd: Path, verbose: bool, quiet: bool, label: str, **kwargs):
    """Mock implementation simulating LLM output for each checkup step."""
    step_id = label.replace("step", "").split("_iter")[0]

    success = True
    cost = 0.50
    provider = "anthropic"
    output = ""

    if step_id == "1":
        output = "Project uses Python 3.12 backend + Next.js 15 frontend."
    elif step_id == "2":
        output = "All dependencies accounted for. No missing packages."
    elif step_id == "3":
        output = "Backend compiles cleanly. Frontend build succeeds."
    elif step_id == "4":
        output = "1 orphan page found: /admin/crm/actions missing from sidebar."
    elif step_id == "5":
        output = "All 3061 backend tests pass. All 1557 frontend tests pass."
    elif step_id == "6_1":
        output = (
            "Fixed orphan page — added CRM Actions to admin sidebar.\n"
            "FILES_CREATED: \n"
            "FILES_MODIFIED: frontend/src/app/admin/layout.tsx"
        )
    elif step_id == "6_2":
        output = (
            "Wrote 3 regression tests for sidebar fix.\n"
            "FILES_CREATED: backend/tests/test_checkup_regressions.py\n"
            "FILES_MODIFIED: frontend/src/app/admin/__test__/layout.test.tsx"
        )
    elif step_id == "6_3":
        output = (
            "Wrote 10 integration tests.\n"
            "FILES_CREATED: backend/tests/test_checkup_e2e.py"
        )
    elif step_id == "7":
        output = "All Issues Fixed. All tests pass. Build clean."
    elif step_id == "8":
        output = "Created PR #42 with all fixes and tests."

    return success, output, cost, provider


def main():
    """Main function to run the checkup orchestrator simulation."""
    print("Starting Agentic Checkup Orchestrator Simulation...")
    print(f"Step order: {STEP_ORDER}")
    print(f"Total display steps: {TOTAL_STEPS}")
    print(f"Max iterations: {MAX_FIX_VERIFY_ITERATIONS}")
    print("-" * 60)

    # Demonstrate helper functions
    print(f"_next_step(2) = {_next_step(2)}")       # 3
    print(f"_next_step(5) = {_next_step(5)}")       # 6.1
    print(f"_next_step(6.1) = {_next_step(6.1)}")   # 6.2
    print(f"_next_step(6.3) = {_next_step(6.3)}")   # 7

    files = _parse_changed_files(
        "FILES_CREATED: src/a.py, src/b.py\n"
        "FILES_MODIFIED: src/c.py"
    )
    print(f"Parsed files: {files}")  # ['src/a.py', 'src/b.py', 'src/c.py']
    print("-" * 60)

    with patch("pdd.agentic_checkup_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
         patch("pdd.agentic_checkup_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
         patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=12345), \
         patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"), \
         patch("pdd.agentic_checkup_orchestrator._setup_worktree", return_value=(Path("/tmp/worktree"), None)):

        success, message, cost, model = run_agentic_checkup_orchestrator(
            issue_url="https://github.com/example/myproject/issues/42",
            issue_content="Check the entire CRM app for health issues.",
            repo_owner="example",
            repo_name="myproject",
            issue_number=42,
            issue_title="CRM Health Check",
            architecture_json='[{"filename": "crm_models_Python.prompt"}]',
            pddrc_content="contexts:\n  default:\n    prompts_dir: prompts",
            cwd=Path("/tmp/myproject"),
            verbose=True,
            quiet=False,
            no_fix=False,
        )

    print("-" * 60)
    print("Simulation Complete.")
    print(f"Success      : {success}")
    print(f"Message      : {message}")
    print(f"Total Cost   : ${cost:.2f}")
    print(f"Model Used   : {model}")


if __name__ == "__main__":
    main()
