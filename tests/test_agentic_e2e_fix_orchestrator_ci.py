import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch
from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

@pytest.fixture
def mock_gh_and_agent():
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_task, \
         patch("pdd.agentic_e2e_fix_orchestrator.subprocess.run") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment") as mock_check_e2e:

        # Default mock behavior
        mock_task.return_value = (True, "LOCAL_TESTS_PASS", 0.0, "gpt-4")
        mock_run.return_value = MagicMock(returncode=0, stdout="822")
        mock_load.return_value = "Mock Prompt Template"
        mock_check_e2e.return_value = (True, "")

        yield {
            "task": mock_task,
            "run": mock_run,
            "load": mock_load,
            "save": mock_save,
            "check_e2e": mock_check_e2e
        }

def test_step10_skips_if_no_pr(mock_gh_and_agent, tmp_path):
    """Verify Step 10 skips CI validation if no PR is found."""
    # Setup: Mock Step 9 to return LOCAL_TESTS_PASS
    # Mock gh pr list to return nothing
    def mock_run_side_effect(cmd, **kwargs):
        if "pr" in cmd and "list" in cmd:
            return MagicMock(returncode=0, stdout="")
        if "rev-parse" in cmd:
            return MagicMock(returncode=0, stdout="feat-branch")
        return MagicMock(returncode=0, stdout="")
    
    mock_gh_and_agent["run"].side_effect = mock_run_side_effect
    
    # Mock tasks for steps 1-9
    mock_gh_and_agent["task"].side_effect = [
        (True, "step1", 0.0, "m"),
        (True, "step2", 0.0, "m"),
        (True, "step3", 0.0, "m"),
        (True, "step4", 0.0, "m"),
        (True, "step5", 0.0, "m"),
        (True, "step6", 0.0, "m"),
        (True, "step7", 0.0, "m"),
        (True, "step8", 0.0, "m"),
        (True, "LOCAL_TESTS_PASS", 0.0, "m"),
    ]

    success, message, cost, model, files = run_agentic_e2e_fix_orchestrator(
        issue_url="https://github.com/owner/repo/issues/822",
        issue_content="Test issue",
        repo_owner="owner",
        repo_name="repo",
        issue_number=822,
        issue_author="author",
        issue_title="title",
        cwd=tmp_path,
        max_cycles=1,
        resume=False,
        quiet=True
    )
    
    assert success is True
    assert "no PR found" in message
    # Should have run 9 tasks
    assert mock_gh_and_agent["task"].call_count == 9
