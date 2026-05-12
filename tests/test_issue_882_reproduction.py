import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path
import click

from pdd.update_main import update_main

@patch('pdd.update_main.update_file_pair')
@patch('pdd.update_main.is_code_changed', return_value=(True, ""))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.architecture_registry.find_architecture_for_project')
@patch('pdd.update_main._find_prd_file')
@patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": True, "updated": True, "changes": {}})
@patch('pdd.agentic_common.run_agentic_task')
def test_issue_882_reproduction(mock_agentic, mock_arch, mock_find_prd, mock_find_arch, mock_git, mock_changed, mock_update, tmp_path, capsys):
    """
    Reproduces issue #882: PRD sync treats run_agentic_task return tuple as text.
    """
    # 1. Provide mock return for the update file pair to consider it successful
    mock_update.return_value = {
        "prompt_file": "prompts/src/module1_python.prompt", 
        "status": "✅ Success", 
        "cost": 0.05, 
        "model": "mock_model", 
        "error": ""
    }
    
    # 2. Mock run_agentic_task to return the tuple as documented in agentic_common.py
    # (success, output, total_cost, model_name)
    mock_agentic.return_value = (True, "<updated-prd>new PRD content</updated-prd>", 0.12, "agent_model")
    
    # 3. Setup workspace: architecture.json and PRD.md must exist
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    arch_file = repo_root / "architecture.json"
    arch_file.write_text("{}")
    
    prd_file = repo_root / "PRD.md"
    prd_file.write_text("old PRD content")
    
    prompts_dir = repo_root / "prompts"
    prompts_dir.mkdir()
    
    mock_find_arch.return_value = [arch_file]
    mock_find_prd.return_value = prd_file

    ctx = click.Context(click.Command('update'))
    ctx.obj = {"verbose": False}

    # Use patch to mock pairs discovery
    with patch('pdd.update_main.find_and_resolve_all_pairs', return_value=[("prompts/src/module1_python.prompt", "src/module1.py")]):
        with patch('pdd.update_main.git.Repo'):
            with patch('pdd.update_main.os.getcwd', return_value=str(repo_root)):
                update_main(
                    ctx=ctx, 
                    use_git=False, 
                    repo=True, 
                    input_prompt_file=None, 
                    modified_code_file=None, 
                    input_code_file=None, 
                    output=None,
                    dry_run=False,
                    sync_metadata=False
                )

    # 4. Assert that the bug is NOT present
    # In the buggy code, run_agentic_task returned tuple is tested with `"<updated-prd>" in llm_output` 
    # which evaluates to False because llm_output is a tuple.
    # Therefore, PRD.md remains "old PRD content".
    #
    # If the bug was fixed, PRD.md would contain "new PRD content".
    assert "new PRD content" in prd_file.read_text(), (
        "Bug reproduction successful: PRD was not updated because the agent's output tuple "
        "was treated as a string, causing the `<updated-prd>` check to fail."
    )

@patch('pdd.update_main.update_file_pair')
@patch('pdd.update_main.is_code_changed', return_value=(True, ""))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.architecture_registry.find_architecture_for_project')
@patch('pdd.update_main._find_prd_file')
@patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": True, "updated": True, "changes": {}})
@patch('pdd.agentic_common.run_agentic_task')
def test_prd_sync_updated(mock_agentic, mock_arch, mock_find_prd, mock_find_arch, mock_git, mock_changed, mock_update, tmp_path, capsys):
    """
    Acceptance Criteria: Add a unit test where mocked run_agentic_task() returns 
    (True, "<updated-prd>new</updated-prd>", 0.12, "agent") and the PRD file is updated.
    """
    mock_update.return_value = {
        "prompt_file": "prompts/src/module1_python.prompt", 
        "status": "✅ Success", 
        "cost": 0.05, 
        "model": "mock_model", 
        "error": ""
    }
    
    mock_agentic.return_value = (True, "<updated-prd>new PRD content</updated-prd>", 0.12, "agent_model")
    
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    arch_file = repo_root / "architecture.json"
    arch_file.write_text("{}")
    
    prd_file = repo_root / "PRD.md"
    prd_file.write_text("old PRD content")
    
    prompts_dir = repo_root / "prompts"
    prompts_dir.mkdir()
    
    mock_find_arch.return_value = [arch_file]
    mock_find_prd.return_value = prd_file

    ctx = click.Context(click.Command('update'))
    ctx.obj = {"verbose": False}

    with patch('pdd.update_main.find_and_resolve_all_pairs', return_value=[("prompts/src/module1_python.prompt", "src/module1.py")]):
        with patch('pdd.update_main.git.Repo'):
            with patch('pdd.update_main.os.getcwd', return_value=str(repo_root)):
                result = update_main(
                    ctx=ctx, 
                    use_git=False, 
                    repo=True, 
                    input_prompt_file=None, 
                    modified_code_file=None, 
                    input_code_file=None, 
                    output=None,
                    dry_run=False,
                    sync_metadata=False
                )

    out = capsys.readouterr().out
    assert "new PRD content" in prd_file.read_text(), "PRD file was not updated."
    assert "PRD status: updated" in out, "PRD status should be updated."
    
    # Assert cost
    assert result is not None
    assert result[1] == 0.17, f"Cost should be 0.17, got {result[1]}"


@patch('pdd.update_main.update_file_pair')
@patch('pdd.update_main.is_code_changed', return_value=(True, ""))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.architecture_registry.find_architecture_for_project')
@patch('pdd.update_main._find_prd_file')
@patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": True, "updated": True, "changes": {}})
@patch('pdd.agentic_common.run_agentic_task')
def test_prd_sync_no_update_needed(mock_agentic, mock_arch, mock_find_prd, mock_find_arch, mock_git, mock_changed, mock_update, tmp_path, capsys):
    """
    Acceptance Criteria: Add a unit test where output is NO_UPDATE_NEEDED and the PRD file remains unchanged.
    """
    mock_update.return_value = {
        "prompt_file": "prompts/src/module1_python.prompt", 
        "status": "✅ Success", 
        "cost": 0.05, 
        "model": "mock_model", 
        "error": ""
    }
    
    mock_agentic.return_value = (True, "NO_UPDATE_NEEDED", 0.05, "agent_model")
    
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    arch_file = repo_root / "architecture.json"
    arch_file.write_text("{}")
    
    prd_file = repo_root / "PRD.md"
    prd_file.write_text("old PRD content")
    
    prompts_dir = repo_root / "prompts"
    prompts_dir.mkdir()
    
    mock_find_arch.return_value = [arch_file]
    mock_find_prd.return_value = prd_file

    ctx = click.Context(click.Command('update'))
    ctx.obj = {"verbose": False}

    with patch('pdd.update_main.find_and_resolve_all_pairs', return_value=[("prompts/src/module1_python.prompt", "src/module1.py")]):
        with patch('pdd.update_main.git.Repo'):
            with patch('pdd.update_main.os.getcwd', return_value=str(repo_root)):
                result = update_main(
                    ctx=ctx, 
                    use_git=False, 
                    repo=True, 
                    input_prompt_file=None, 
                    modified_code_file=None, 
                    input_code_file=None, 
                    output=None,
                    dry_run=False,
                    sync_metadata=False
                )

    out = capsys.readouterr().out
    assert "PRD status: unchanged" in out, "PRD status should be unchanged."
    assert "old PRD content" in prd_file.read_text(), "PRD file should remain unchanged."
    
    # Assert cost
    assert result is not None
    assert result[1] == 0.10, f"Cost should be 0.10, got {result[1]}"


@patch('pdd.update_main.update_file_pair')
@patch('pdd.update_main.is_code_changed', return_value=(True, ""))
@patch('pdd.update_main.get_git_changed_files', return_value=set())
@patch('pdd.architecture_registry.find_architecture_for_project')
@patch('pdd.update_main._find_prd_file')
@patch('pdd.architecture_sync.update_architecture_from_prompt', return_value={"success": True, "updated": True, "changes": {}})
@patch('pdd.agentic_common.run_agentic_task')
def test_prd_sync_failure(mock_agentic, mock_arch, mock_find_prd, mock_find_arch, mock_git, mock_changed, mock_update, tmp_path, capsys):
    """
    Acceptance Criteria: Add a unit test where the agent fails and prd_status records the error 
    without crashing the whole repo update.
    """
    mock_update.return_value = {
        "prompt_file": "prompts/src/module1_python.prompt", 
        "status": "✅ Success", 
        "cost": 0.05, 
        "model": "mock_model", 
        "error": ""
    }
    
    # Mock run_agentic_task failure
    mock_agentic.return_value = (False, "API Limit reached", 0.0, "agent_model")
    
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    arch_file = repo_root / "architecture.json"
    arch_file.write_text("{}")
    
    prd_file = repo_root / "PRD.md"
    prd_file.write_text("old PRD content")
    
    prompts_dir = repo_root / "prompts"
    prompts_dir.mkdir()
    
    mock_find_arch.return_value = [arch_file]
    mock_find_prd.return_value = prd_file

    ctx = click.Context(click.Command('update'))
    ctx.obj = {"verbose": False}

    with patch('pdd.update_main.find_and_resolve_all_pairs', return_value=[("prompts/src/module1_python.prompt", "src/module1.py")]):
        with patch('pdd.update_main.git.Repo'):
            with patch('pdd.update_main.os.getcwd', return_value=str(repo_root)):
                update_main(
                    ctx=ctx, 
                    use_git=False, 
                    repo=True, 
                    input_prompt_file=None, 
                    modified_code_file=None, 
                    input_code_file=None, 
                    output=None,
                    dry_run=False,
                    sync_metadata=False
                )

    out = capsys.readouterr().out
    
    # It shouldn't crash, and the failure should be recorded in prd_status
    assert "PRD status: unchanged" not in out, "PRD status should not be unchanged on failure."
    assert "API Limit reached" in out, "Failure reason should be in the output."

