from __future__ import annotations

import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from rich.console import Console

project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

console = Console()


def mock_load_prompt_template(template_name: str) -> str:
    """Return a minimal prompt template for the requested step."""
    return (
        f"Template: {template_name}\n"
        "Issue #{issue_number}\n"
        "Cycle {cycle_number}/{max_cycles}\n"
        "Protect tests: {protect_tests_flag}"
    )


def mock_run_agentic_task(
    instruction: str,
    cwd: Path,
    *,
    label: str,
    **_: object,
) -> tuple[bool, str, float, str]:
    """Simulate a successful single-cycle E2E fix workflow."""
    if "step1" in label:
        return True, "Unit tests reproduced the failure.", 0.04, "gpt-4.1"
    if "step2" in label:
        return True, "E2E tests failed in the login flow.", 0.04, "gpt-4.1"
    if "step3" in label:
        return True, "CODE_BUG: stale retry logic.", 0.05, "gpt-4.1"
    if "step4" in label:
        return True, "Applied targeted E2E fix.\nFILES_MODIFIED: src/login.py", 0.06, "gpt-4.1"
    if "step5" in label:
        return True, "DEV_UNITS_IDENTIFIED: src/login.py", 0.05, "gpt-4.1"
    if "step6" in label:
        return True, "FILES_CREATED: tests/test_login.py", 0.05, "gpt-4.1"
    if "step7" in label:
        return True, "The new unit test fails before the fix and passes after it.", 0.05, "gpt-4.1"
    if "step8" in label:
        return True, "src/login.py: FIXED\nFILES_MODIFIED: src/login.py, tests/test_login.py", 0.08, "gpt-4.1"
    if "step9" in label:
        return True, "Verification complete.\nALL_TESTS_PASS", 0.05, "gpt-4.1"
    return False, f"Unexpected label: {label}", 0.0, "gpt-4.1"


def main() -> None:
    """Run a local demonstration of the orchestrator with mocked dependencies."""
    with TemporaryDirectory() as temp_dir:
        cwd = Path(temp_dir)
        console.print(f"[blue]Running mocked E2E fix workflow in {cwd}[/blue]")

        with patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
            patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
            patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
            patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None), \
            patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
            patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment", return_value=(True, "")), \
            patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=["tests/test_login.py"]), \
            patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently", return_value=(True, "1 passed")), \
            patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
            patch(
                "pdd.agentic_e2e_fix_orchestrator._detect_changed_files",
                return_value=["src/login.py", "tests/test_login.py"],
            ), \
            patch(
                "pdd.agentic_e2e_fix_orchestrator._commit_and_push",
                return_value=(True, "Committed and pushed 2 file(s)"),
            ), \
            patch(
                "pdd.agentic_e2e_fix_orchestrator.run_ci_validation_loop",
                return_value=(True, "CI validation passed after push.", 0.02),
            ):
            success, final_message, total_cost, model_used, changed_files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/example-owner/example-repo/issues/123",
                issue_content="Login E2E test fails after a retry timeout.",
                repo_owner="example-owner",
                repo_name="example-repo",
                issue_number=123,
                issue_author="example-author",
                issue_title="Fix login E2E retry failure",
                cwd=cwd,
                timeout_adder=0.0,
                max_cycles=1,
                resume=False,
                verbose=False,
                quiet=False,
                use_github_state=False,
                protect_tests=True,
                ci_retries=3,
                skip_ci=False,
            )

        console.print("\n[bold]Results[/bold]")
        console.print(f"Success: {success}")
        console.print(f"Final message: {final_message}")
        console.print(f"Total cost: ${total_cost:.2f}")
        console.print(f"Model used: {model_used}")
        console.print(f"Changed files: {changed_files}")


if __name__ == "__main__":
    main()
